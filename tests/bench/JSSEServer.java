/* ------------------------------------------------------------------------ */
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.Socket;
import java.security.KeyStore;
import java.security.Principal;
import java.security.PrivateKey;
import java.security.cert.X509Certificate;

import javax.net.ssl.KeyManager;
import javax.net.ssl.KeyManagerFactory;
import javax.net.ssl.SSLContext;
import javax.net.ssl.SSLServerSocket;
import javax.net.ssl.SSLServerSocketFactory;
import javax.net.ssl.SSLSocket;
import javax.net.ssl.TrustManagerFactory;
import javax.net.ssl.X509KeyManager;

/* ------------------------------------------------------------------------ */
public class JSSEServer {
    private static SSLContext sslcontext = null;

    private static class MyKeyManager implements X509KeyManager {
        protected X509KeyManager target;

        public MyKeyManager(X509KeyManager target) {
            this.target = target;
        }

        @Override
        public String chooseClientAlias(String[] keyType, Principal[] issuers, Socket socket) {
            return target.chooseClientAlias(keyType, issuers, socket);
        }

        @Override
        public String chooseServerAlias(String keyType, Principal[] issuers, Socket socket) {
            String certname = System.getenv("CERTNAME");

            if (certname == null)
                throw new RuntimeException("CERTNAME not set");
            return String.format("utls pki (%s)", certname);
        }

        @Override
        public X509Certificate[] getCertificateChain(String alias) {
            return target.getCertificateChain(alias);
        }

        @Override
        public String[] getClientAliases(String keyType, Principal[] issuers) {
            return target.getClientAliases(keyType, issuers);
        }

        @Override
        public PrivateKey getPrivateKey(String alias) {
            return target.getPrivateKey(alias);
        }

        @Override
        public String[] getServerAliases(String keyType, Principal[] issuers) {
            return target.getServerAliases(keyType, issuers);
        }
    }

    static {
        try {
            String pki = System.getenv("PKI");

            if (pki == null)
                throw new RuntimeException("PKI not set");

            TrustManagerFactory tmf = TrustManagerFactory.getInstance("SunX509");
            KeyManagerFactory kmf = KeyManagerFactory.getInstance("SunX509");
            KeyStore ks = KeyStore.getInstance("JKS");

            ks.load(new FileInputStream(pki + "/JSK.db"), "123456".toCharArray());
            kmf.init(ks, new char[] {});
            tmf.init(ks);

            sslcontext = SSLContext.getInstance("TLSv1.2");
            sslcontext.init(
                    new KeyManager[] { new MyKeyManager((X509KeyManager) kmf.getKeyManagers()[0]) },
                    tmf.getTrustManagers(), null);
            sslcontext.getServerSessionContext().setSessionCacheSize(0);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    private static SSLServerSocket createServerSocket() throws IOException {
        SSLServerSocketFactory sslserversocketfactory =
                sslcontext.getServerSocketFactory();
        return (SSLServerSocket) sslserversocketfactory.createServerSocket(5000);
    }

    private static class ServerEntry implements Runnable {
        private SSLServerSocket socket;

        public ServerEntry(SSLServerSocket socket) {
            this.socket = socket;
        }

        @Override
        public synchronized void run() {
            try {
                final byte[] buffer = new byte[1024 * 1024];

                while (true) {
                    SSLSocket sslsocket = (SSLSocket) this.socket.accept();
                    sslsocket.startHandshake();

                    InputStream input = sslsocket.getInputStream();

                    while (true) {
                        if (input.read(buffer) < 0)
                            break ;
                    }
                    sslsocket.close();
                }
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        }
    }

    static public void main(String[] args) throws Exception {
        ServerEntry server = new ServerEntry(JSSEServer.createServerSocket());
        server.run();
    }
}
