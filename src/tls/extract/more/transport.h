#ifdef __FStar_H_DEFINED

#ifndef __TRANSPORT_H
#define __TRANSPORT_H
// TCP stuff ... to be implemented by hand.

FStar_Error_optResult__Prims_string___
(*Transport___proj__Mkt__item__snd(Transport_t projectee))(FStar_Bytes_bytes x0);

FStar_Tcp_recv_result____
(*Transport___proj__Mkt__item__rcv(Transport_t projectee))(Prims_nat x0);

Transport_t
Transport_callbacks(
  FStar_Error_optResult__Prims_string___ (*send1)(FStar_Bytes_bytes x0),
  FStar_Tcp_recv_result____ (*recv1)(Prims_nat x0)
);

Transport_t Transport_wrap(FStar_Tcp_networkStream tcp);

typedef FStar_Tcp_tcpListener Transport_tcpListener;

FStar_Tcp_tcpListener Transport_listen(Prims_string domain1, Prims_nat port);

Transport_t Transport_accept(FStar_Tcp_tcpListener listener);

Transport_t Transport_connect(Prims_string domain1, Prims_nat port);

extern void (*Transport_close)(FStar_Tcp_networkStream x0);

FStar_Error_optResult__Prims_string___ Transport_send(Transport_t tcp, FStar_Bytes_bytes data);

FStar_Tcp_recv_result____ Transport_recv(Transport_t tcp, Prims_nat len1);

void Transport_test(Transport_t tcp, FStar_Bytes_bytes data);

FStar_Tcp_recv_result____
Transport_really_read_rec(FStar_Bytes_bytes prev, Transport_t tcp, Prims_nat len1);

extern FStar_Tcp_recv_result____ (*Transport_really_read)(Transport_t x0, Prims_nat x1);

#endif
#endif
