let _ = Callback.register "MITLS_FFI_Config" FFI.ffiConfig;
        Callback.register "MITLS_FFI_SetCertChainFile" FFI.ffiSetCertChainFile;
        Callback.register "MITLS_FFI_SetPrivateKeyFile" FFI.ffiSetPrivateKeyFile;
        Callback.register "MITLS_FFI_SetCAFile" FFI.ffiSetCAFile;
        Callback.register "MITLS_FFI_SetCipherSuites" FFI.ffiSetCipherSuites;
        Callback.register "MITLS_FFI_SetSignatureAlgorithms" FFI.ffiSetSignatureAlgorithms;
        Callback.register "MITLS_FFI_SetNamedGroups" FFI.ffiSetNamedGroups;
        Callback.register "MITLS_FFI_Connect"  FFI.ffiConnect;
        Callback.register "MITLS_FFI_AcceptConnected"  FFI.ffiAcceptConnected;
        Callback.register "MITLS_FFI_Send" FFI.ffiSend;
        Callback.register "MITLS_FFI_Recv" FFI.ffiRecv;
        
