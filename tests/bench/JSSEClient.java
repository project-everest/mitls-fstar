/* ------------------------------------------------------------------------ */
import java.io.FileInputStream;
import java.io.OutputStream;
import java.net.Socket;
import java.security.KeyStore;
import java.security.Principal;
import java.security.PrivateKey;
import java.security.Provider;
import java.security.Security;
import java.security.cert.X509Certificate;
import java.util.Random;

import javax.net.ssl.KeyManager;
import javax.net.ssl.KeyManagerFactory;
import javax.net.ssl.SSLContext;
import javax.net.ssl.SSLException;
import javax.net.ssl.SSLSocket;
import javax.net.ssl.SSLSocketFactory;
import javax.net.ssl.TrustManagerFactory;
import javax.net.ssl.X509KeyManager;

import org.bouncycastle.jce.provider.BouncyCastleProvider;

/* ------------------------------------------------------------------------ */
public class JSSEClient {
    private static byte[] data = new byte[1024 * 1024];

    static {
        (new Random()).nextBytes(JSSEClient.data);
    }

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

    private static void configureSSLSocket(SSLSocket socket, boolean isserver) {
        String cipher = System.getenv("CIPHERSUITE");

        if (cipher == null)
            throw new RuntimeException("CIPHERSUITE not set");
        try {
            socket.setEnabledCipherSuites(new String[] { cipher });
        } catch (IllegalArgumentException e) {
            socket.setEnabledCipherSuites(new String[] { cipher.replaceFirst("^TLS_",  "SSL_") });
        }
    }

    private static class ClientEntry implements Runnable {
        private long totaltxsent  = 0;
        private long totaltxticks = 0;
        private long totalhs      = 0;
        private long totalhsticks = 0;

        @Override
        public synchronized void run() {
            final int blksize = 1024;
            
            int failures = 0;

            try {
                SSLSocketFactory sslsocketfactory = sslcontext.getSocketFactory();

                for (int i = 0; i < 200; ++i) {
                    byte[] bytea = { 0x00 };

                    Socket rsocket  = new Socket("127.0.0.1", 5000);
                    String hostname = rsocket.getInetAddress().getHostName();

                    long t1  = System.nanoTime() / 1000;

                    SSLSocket socket = null;
                            
                    try {                    
                        socket = (SSLSocket) sslsocketfactory.createSocket(rsocket, hostname, rsocket.getPort(), true);
                        JSSEClient.configureSSLSocket(socket, false);
                        // From documentation:  This method is synchronous for the initial handshake on
                        // a connection and returns when the negotiated handshake is complete.
                        socket.startHandshake();
                    } catch (SSLException e) {
                        if (socket != null) {
                            try {
                                socket.close();
                            } catch (Exception ie) {}
                        }
                        socket = null;
                        if (++failures < 10) {
                            System.err.println(e);
                            continue ;
                        }
                        throw e;
                    }
                    
                    socket.getOutputStream().write(bytea, 0, 1);

                    long t2 = System.nanoTime() / 1000;

                    socket.close();

                    if (i != 0) {
                        totalhs      += 1;
                        totalhsticks += (t2 - t1);
                    }
                }

                SSLSocket socket = null;
                
                while (true) {
                    try {
                        socket = (SSLSocket) sslsocketfactory.createSocket("127.0.0.1", 5000);
                        JSSEClient.configureSSLSocket(socket, false);
                        socket.startHandshake();
                    } catch (SSLException e) {
                        if (socket != null) {
                            try {
                                socket.close();
                            } catch (Exception ie) {}
                        }
                        socket = null;
                        if (++failures < 10) {
                            System.err.println(e);
                            continue ;
                        }
                        throw e;
                    }
                    
                    break ;
                }

                OutputStream output = socket.getOutputStream();

                int sent = 0;
                int upos = 0;

                final long t1 = System.nanoTime() / 1000;

                while (sent < 128 * 1024 * 1024) {
                    if (JSSEClient.data.length - upos < blksize)
                        upos = 0;
                    output.write(JSSEClient.data, upos, blksize);
                    sent += blksize;
                    upos += blksize;
                }
                output.flush();

                final long t2 = System.nanoTime() / 1000;

                this.totaltxsent  = sent;
                this.totaltxticks = t2 - t1;

                socket.close();
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        }

        public long getTotaltxsent() {
            return this.totaltxsent;
        }

        public long getTotaltxticks() {
            return this.totaltxticks;
        }

        public long getTotalhs() {
            return this.totalhs;
        }

        public long getTotalhsticks() {
            return this.totalhsticks;
        }
    }

    static {
        if ("1".equals(System.getenv("USEBC"))) {
            System.err.println("Using BC as Security Provider");
            Security.addProvider(new BouncyCastleProvider());
            for (Provider provider : Security.getProviders()) {
                System.err.println("Security Provider: " + provider);
            }
        }
    }

    static public void main(String[] args) throws Exception {
        ClientEntry client = new ClientEntry();
        client.run();

        if (client.getTotaltxticks() > 0) {
            System.out.format("%s: %.2f HS/s\n",
                    System.getenv("CIPHERSUITE"),
                    client.getTotalhs()
                    / (((double) client.getTotalhsticks()) / 1000000));

            System.out.format("%s: %.2f MiB/s\n",
                    System.getenv("CIPHERSUITE"),
                    client.getTotaltxsent()
                    / ((double) (1024 * 1024))
                    / (((double) client.getTotaltxticks()) / 1000000));
        }
    }
}
