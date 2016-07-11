let wrappedConnect12 config host = 
    TestClient.ffiConnect12 () () () () () () config host

let _ = Callback.register "MITLS_FFI_Config" TestClient13.ffiConfig;
        Callback.register "MITLS_FFI_Connect12" wrappedConnect12;
        Callback.register "MITLS_FFI_Connect13" TestClient13.ffiConnect13;
