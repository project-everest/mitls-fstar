#pragma once

typedef struct newtworkStream {} Platform_Tcp_networkStream;
typedef struct tcpListener {} Platform_Tcp_tcpListener;

// void Platform_Tcp_set_nonblock(Platform_Tcp_networkStream stream);
// void Platform_Tcp_clear_nonblock(Platform_Tcp_networkStream stream);

// // Server side

// void listen(const char * hostname, int port);
// void acceptTimeout(int port, Platform_Tcp_tcpListener listener);
// Platform_Tcp_networkStream accept(Platform_Tcp_tcpListener listener);
// void stop(Platform_Tcp_tcpListener listener);

// // Client side

// Platform_Tcp_networkStream connectTimeout(int, const char * str, int);
// Platform_Tcp_networkStream connect(const char * hostname, int port);

// Input/Output

// adding support for (potentially) non-blocking I/O
// NB for now, send *fails* on partial writes, and *loops* on EAGAIN/EWOULDBLOCK.

// type recv_result (max:nat) =
//   | RecvWouldBlock
//   | RecvError of string
//   | Received of b:bytes {length b <= max}
// assume val recv_async: Platform_Tcp_networkStream -> max:nat -> EXT (recv_result max)

// assume val recv: Platform_Tcp_networkStream -> max:nat -> EXT (optResult string (b:bytes {length b <= max}))
// assume val send: Platform_Tcp_networkStream -> bytes -> EXT (optResult string unit)
// assume val close: Platform_Tcp_networkStream -> EXT unit

// (* Create a network stream from a given stream.
//    Only used by the application interface TLSharp. *)
// (* assume val create: System.IO.Stream -> Platform_Tcp_networkStream*)
