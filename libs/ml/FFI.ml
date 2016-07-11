let wrappedConnect12 config host = 
    TLSClient.connect () () () () () () config host

let _ = Callback.register "MITLS_FFI_Config" TLSClient13.configure;
        Callback.register "MITLS_FFI_Connect12" wrappedConnect12;
        Callback.register "MITLS_FFI_Connect13" TLSClient13.connect;
