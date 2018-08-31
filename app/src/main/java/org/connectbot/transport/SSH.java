/*
 * ConnectBot: simple, powerful, open-source SSH client for Android
 * Copyright 2007 Kenny Root, Jeffrey Sharkey
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.connectbot.transport;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.connectbot.R;
import org.connectbot.bean.HostBean;
import org.connectbot.service.TerminalBridge;
import org.connectbot.service.TerminalManager;
import org.connectbot.util.Ed25519Provider;
import org.connectbot.util.HostDatabase;

import android.content.Context;
import android.net.Uri;
import android.util.Log;

import com.trilead.ssh2.ChannelCondition;
import com.trilead.ssh2.Connection;
import com.trilead.ssh2.ConnectionInfo;
import com.trilead.ssh2.ConnectionMonitor;
import com.trilead.ssh2.ExtendedServerHostKeyVerifier;
import com.trilead.ssh2.InteractiveCallback;
import com.trilead.ssh2.KnownHosts;
import com.trilead.ssh2.Session;

/**
 * @author Kenny Root
 *
 */
public class SSH extends AbsTransport implements ConnectionMonitor, InteractiveCallback{
	static {
		// Since this class deals with EdDSA keys, we need to make sure this is available.
		Ed25519Provider.insertIfNeeded();
	}

	public SSH() {
		super();
	}

	/**
	 * @param host
	 * @param bridge
	 * @param manager
	 */
	public SSH(HostBean host, TerminalBridge bridge, TerminalManager manager) {
		super(host, bridge, manager);
	}

	private static final String PROTOCOL = "ssh";
	private static final String TAG = "CB.SSH";
	private static final int DEFAULT_PORT = 22;

	private static final String AUTH_PUBLICKEY = "publickey",
		AUTH_PASSWORD = "password",
		AUTH_KEYBOARDINTERACTIVE = "keyboard-interactive";

	private final static int AUTH_TRIES = 20;

	private static final Pattern hostmask = Pattern.compile(
			"^(.+)@(([0-9a-z.-]+)|(\\[[a-f:0-9]+\\]))(:(\\d+))?$", Pattern.CASE_INSENSITIVE);

	private boolean compression = false;
	private volatile boolean authenticated = false;
	private volatile boolean connected = false;
	private volatile boolean sessionOpen = false;

	private boolean interactiveCanContinue = true;

	private Connection connection;
	private Session session;

	private OutputStream stdin;
	private InputStream stdout;
	private InputStream stderr;

	private static final int conditions = ChannelCondition.STDOUT_DATA
		| ChannelCondition.STDERR_DATA
		| ChannelCondition.CLOSED
		| ChannelCondition.EOF;

	private int columns;
	private int rows;

	private int width;
	private int height;

	private String agentLockPassphrase;

	public class HostKeyVerifier extends ExtendedServerHostKeyVerifier {
		@Override
		public boolean verifyServerHostKey(String hostname, int port,
				String serverHostKeyAlgorithm, byte[] serverHostKey) throws IOException {

			// read in all known hosts from hostdb
			KnownHosts hosts = manager.hostdb.getKnownHosts();
			Boolean result;

			String matchName = String.format(Locale.US, "%s:%d", hostname, port);

			String fingerprint = KnownHosts.createHexFingerprint(serverHostKeyAlgorithm, serverHostKey);

			String algorithmName;
			if ("ssh-rsa".equals(serverHostKeyAlgorithm))
				algorithmName = "RSA";
			else if ("ssh-dss".equals(serverHostKeyAlgorithm))
				algorithmName = "DSA";
			else if (serverHostKeyAlgorithm.startsWith("ecdsa-"))
				algorithmName = "EC";
			else if ("ssh-ed25519".equals(serverHostKeyAlgorithm))
				algorithmName = "Ed25519";
			else
				algorithmName = serverHostKeyAlgorithm;

			switch (hosts.verifyHostkey(matchName, serverHostKeyAlgorithm, serverHostKey)) {
			case KnownHosts.HOSTKEY_IS_OK:
				bridge.outputLine(manager.res.getString(R.string.terminal_sucess, algorithmName, fingerprint));
				return true;

			case KnownHosts.HOSTKEY_IS_NEW:
				// prompt user
				bridge.outputLine(manager.res.getString(R.string.host_authenticity_warning, hostname));
				bridge.outputLine(manager.res.getString(R.string.host_fingerprint, algorithmName, fingerprint));

				result = bridge.promptHelper.requestBooleanPrompt(null, manager.res.getString(R.string.prompt_continue_connecting));
				if (result == null) {
					return false;
				}
				if (result) {
					// save this key in known database
					manager.hostdb.saveKnownHost(hostname, port, serverHostKeyAlgorithm, serverHostKey);
				}
				return result;

			case KnownHosts.HOSTKEY_HAS_CHANGED:
				String header = String.format("@   %s   @",
						manager.res.getString(R.string.host_verification_failure_warning_header));

				char[] atsigns = new char[header.length()];
				Arrays.fill(atsigns, '@');
				String border = new String(atsigns);

				bridge.outputLine(border);
				bridge.outputLine(header);
				bridge.outputLine(border);

				bridge.outputLine(manager.res.getString(R.string.host_verification_failure_warning));

				bridge.outputLine(String.format(manager.res.getString(R.string.host_fingerprint),
						algorithmName, fingerprint));

				// Users have no way to delete keys, so we'll prompt them for now.
				result = bridge.promptHelper.requestBooleanPrompt(null, manager.res.getString(R.string.prompt_continue_connecting));
				if (result != null && result) {
					// save this key in known database
					manager.hostdb.saveKnownHost(hostname, port, serverHostKeyAlgorithm, serverHostKey);
					return true;
				} else {
					return false;
				}

			default:
				bridge.outputLine(manager.res.getString(R.string.terminal_failed));
				return false;
			}
		}

		@Override
		public List<String> getKnownKeyAlgorithmsForHost(String host, int port) {
			return manager.hostdb.getHostKeyAlgorithmsForHost(host, port);
		}

		@Override
		public void removeServerHostKey(String host, int port, String algorithm, byte[] hostKey) {
			manager.hostdb.removeKnownHost(host, port, algorithm, hostKey);
		}

		@Override
		public void addServerHostKey(String host, int port, String algorithm, byte[] hostKey) {
			manager.hostdb.saveKnownHost(host, port, algorithm, hostKey);
		}
	}

	private void authenticate() {
		try {
			if (connection.authenticateWithNone(host.getUsername())) {
				finishConnection();
				return;
			}
		} catch (Exception e) {
			Log.d(TAG, "Host does not support 'none' authentication.");
		}

		bridge.outputLine(manager.res.getString(R.string.terminal_auth));

		try {
			if (interactiveCanContinue && connection.isAuthMethodAvailable(host.getUsername(), AUTH_KEYBOARDINTERACTIVE)) {
				// this auth method will talk with us using InteractiveCallback interface
				// it blocks until authentication finishes
				bridge.outputLine(manager.res.getString(R.string.terminal_auth_ki));
				interactiveCanContinue = false;
				if (connection.authenticateWithKeyboardInteractive(host.getUsername(), this)) {
					finishConnection();
				} else {
					bridge.outputLine(manager.res.getString(R.string.terminal_auth_ki_fail));
				}
			} else if (connection.isAuthMethodAvailable(host.getUsername(), AUTH_PASSWORD)) {
				bridge.outputLine(manager.res.getString(R.string.terminal_auth_pass));
				String password = bridge.getPromptHelper().requestStringPrompt(null,
						manager.res.getString(R.string.prompt_password));
				if (password != null
						&& connection.authenticateWithPassword(host.getUsername(), password)) {
					finishConnection();
				} else {
					bridge.outputLine(manager.res.getString(R.string.terminal_auth_pass_fail));
				}
			} else {
				bridge.outputLine(manager.res.getString(R.string.terminal_auth_fail));
			}
		} catch (IllegalStateException e) {
			Log.e(TAG, "Connection went away while we were trying to authenticate", e);
			return;
		} catch (Exception e) {
			Log.e(TAG, "Problem during handleAuthentication()", e);
		}
	}

	/**
	 * Internal method to request actual PTY terminal once we've finished
	 * authentication. If called before authenticated, it will just fail.
	 */
	private void finishConnection() {
		authenticated = true;

		if (!host.getWantSession()) {
			bridge.outputLine(manager.res.getString(R.string.terminal_no_session));
			bridge.onConnected();
			return;
		}

		try {
			session = connection.openSession();

			session.requestPTY(getEmulation(), columns, rows, width, height, null);
			session.startShell();

			stdin = session.getStdin();
			stdout = session.getStdout();
			stderr = session.getStderr();

			sessionOpen = true;

			bridge.onConnected();
		} catch (IOException e1) {
			Log.e(TAG, "Problem while trying to create PTY in finishConnection()", e1);
		}

	}

	@Override
	public void connect() {
		connection = new Connection(host.getHostname(), host.getPort());
		connection.addConnectionMonitor(this);

		try {
			connection.setCompression(compression);
		} catch (IOException e) {
			Log.e(TAG, "Could not enable compression!", e);
		}

		try {
			/* Uncomment when debugging SSH protocol:
			DebugLogger logger = new DebugLogger() {

				public void log(int level, String className, String message) {
					Log.d("SSH", message);
				}

			};
			Logger.enabled = true;
			Logger.logger = logger;
			*/
			ConnectionInfo connectionInfo = connection.connect(new HostKeyVerifier());
			connected = true;

			bridge.outputLine(manager.res.getString(R.string.terminal_kex_algorithm,
					connectionInfo.keyExchangeAlgorithm));
			if (connectionInfo.clientToServerCryptoAlgorithm
					.equals(connectionInfo.serverToClientCryptoAlgorithm)
					&& connectionInfo.clientToServerMACAlgorithm
							.equals(connectionInfo.serverToClientMACAlgorithm)) {
				bridge.outputLine(manager.res.getString(R.string.terminal_using_algorithm,
						connectionInfo.clientToServerCryptoAlgorithm,
						connectionInfo.clientToServerMACAlgorithm));
			} else {
				bridge.outputLine(manager.res.getString(
						R.string.terminal_using_c2s_algorithm,
						connectionInfo.clientToServerCryptoAlgorithm,
						connectionInfo.clientToServerMACAlgorithm));

				bridge.outputLine(manager.res.getString(
						R.string.terminal_using_s2c_algorithm,
						connectionInfo.serverToClientCryptoAlgorithm,
						connectionInfo.serverToClientMACAlgorithm));
			}
		} catch (IOException e) {
			Log.e(TAG, "Problem in SSH connection thread during authentication", e);

			// Display the reason in the text.
			Throwable t = e.getCause();
			do {
				bridge.outputLine(t.getMessage());
				t = t.getCause();
			} while (t != null);

			close();
			onDisconnect();
			return;
		}

		try {
			// enter a loop to keep trying until authentication
			int tries = 0;
			while (connected && !connection.isAuthenticationComplete() && tries++ < AUTH_TRIES) {
				authenticate();

				// sleep to make sure we dont kill system
				Thread.sleep(1000);
			}
		} catch (Exception e) {
			Log.e(TAG, "Problem in SSH connection thread during authentication", e);
		}
	}

	@Override
	public void close() {
		connected = false;

		if (session != null) {
			session.close();
			session = null;
		}

		if (connection != null) {
			connection.close();
			connection = null;
		}
	}

	private void onDisconnect() {
		bridge.dispatchDisconnect(false);
	}

	@Override
	public void flush() throws IOException {
		if (stdin != null)
			stdin.flush();
	}

	@Override
	public int read(byte[] buffer, int start, int len) throws IOException {
		int bytesRead = 0;

		if (session == null)
			return 0;

		int newConditions = session.waitForCondition(conditions, 0);

		if ((newConditions & ChannelCondition.STDOUT_DATA) != 0) {
			bytesRead = stdout.read(buffer, start, len);
		}

		if ((newConditions & ChannelCondition.STDERR_DATA) != 0) {
			byte discard[] = new byte[256];
			while (stderr.available() > 0) {
				stderr.read(discard);
			}
		}

		if ((newConditions & ChannelCondition.EOF) != 0) {
			close();
			onDisconnect();
			throw new IOException("Remote end closed connection");
		}

		return bytesRead;
	}

	@Override
	public void write(byte[] buffer) throws IOException {
		if (stdin != null)
			stdin.write(buffer);
	}

	@Override
	public void write(int c) throws IOException {
		if (stdin != null)
			stdin.write(c);
	}

	@Override
	public Map<String, String> getOptions() {
		Map<String, String> options = new HashMap<>();

		options.put("compression", Boolean.toString(compression));

		return options;
	}

	@Override
	public void setOptions(Map<String, String> options) {
		if (options.containsKey("compression"))
			compression = Boolean.parseBoolean(options.get("compression"));
	}

	public static String getProtocolName() {
		return PROTOCOL;
	}

	@Override
	public boolean isSessionOpen() {
		return sessionOpen;
	}

	@Override
	public boolean isConnected() {
		return connected;
	}

	@Override
	public void connectionLost(Throwable reason) {
		onDisconnect();
	}



	@Override
	public void setDimensions(int columns, int rows, int width, int height) {
		this.columns = columns;
		this.rows = rows;

		if (sessionOpen) {
			try {
				session.resizePTY(columns, rows, width, height);
			} catch (IOException e) {
				Log.e(TAG, "Couldn't send resize PTY packet", e);
			}
		}
	}

	@Override
	public int getDefaultPort() {
		return DEFAULT_PORT;
	}

	@Override
	public String getDefaultNickname(String username, String hostname, int port) {
		if (port == DEFAULT_PORT) {
			return String.format(Locale.US, "%s@%s", username, hostname);
		} else {
			return String.format(Locale.US, "%s@%s:%d", username, hostname, port);
		}
	}

	public static Uri getUri(String input) {
		Matcher matcher = hostmask.matcher(input);

		if (!matcher.matches())
			return null;

		StringBuilder sb = new StringBuilder();

		sb.append(PROTOCOL)
			.append("://")
			.append(Uri.encode(matcher.group(1)))
			.append('@')
			.append(Uri.encode(matcher.group(2)));

		String portString = matcher.group(6);
		int port = DEFAULT_PORT;
		if (portString != null) {
			try {
				port = Integer.parseInt(portString);
				if (port < 1 || port > 65535) {
					port = DEFAULT_PORT;
				}
			} catch (NumberFormatException nfe) {
				// Keep the default port
			}
		}

		if (port != DEFAULT_PORT) {
			sb.append(':')
				.append(port);
		}

		sb.append("/#")
			.append(Uri.encode(input));

		Uri uri = Uri.parse(sb.toString());

		return uri;
	}

	/**
	 * Handle challenges from keyboard-interactive authentication mode.
	 */
	@Override
	public String[] replyToChallenge(String name, String instruction, int numPrompts, String[] prompt, boolean[] echo) {
		interactiveCanContinue = true;
		String[] responses = new String[numPrompts];
		for (int i = 0; i < numPrompts; i++) {
			// request response from user for each prompt
			responses[i] = bridge.promptHelper.requestStringPrompt(instruction, prompt[i]);
		}
		return responses;
	}

	@Override
	public HostBean createHost(Uri uri) {
		HostBean host = new HostBean();

		host.setProtocol(PROTOCOL);

		host.setHostname(uri.getHost());

		int port = uri.getPort();
		if (port < 0)
			port = DEFAULT_PORT;
		host.setPort(port);

		host.setUsername(uri.getUserInfo());

		String nickname = uri.getFragment();
		if (nickname == null || nickname.length() == 0) {
			host.setNickname(getDefaultNickname(host.getUsername(),
					host.getHostname(), host.getPort()));
		} else {
			host.setNickname(uri.getFragment());
		}

		return host;
	}

	@Override
	public void getSelectionArgs(Uri uri, Map<String, String> selection) {
		selection.put(HostDatabase.FIELD_HOST_PROTOCOL, PROTOCOL);
		selection.put(HostDatabase.FIELD_HOST_NICKNAME, uri.getFragment());
		selection.put(HostDatabase.FIELD_HOST_HOSTNAME, uri.getHost());

		int port = uri.getPort();
		if (port < 0)
			port = DEFAULT_PORT;
		selection.put(HostDatabase.FIELD_HOST_PORT, Integer.toString(port));
		selection.put(HostDatabase.FIELD_HOST_USERNAME, uri.getUserInfo());
	}

	@Override
	public void setCompression(boolean compression) {
		this.compression = compression;
	}

	public static String getFormatHint(Context context) {
		return String.format("%s@%s:%s",
				context.getString(R.string.format_username),
				context.getString(R.string.format_hostname),
				context.getString(R.string.format_port));
	}

	/* (non-Javadoc)
	 * @see org.connectbot.transport.AbsTransport#usesNetwork()
	 */
	@Override
	public boolean usesNetwork() {
		return true;
	}
}
