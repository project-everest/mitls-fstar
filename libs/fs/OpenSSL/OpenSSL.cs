using System;
using System.Collections.Generic;
using System.Security.Permissions;
using System.Runtime.InteropServices;

namespace OpenSSL
{
    /* ---------------------------------------------------------------------- */
    public sealed class Config
    {
#if __MonoCS__
        public const string DLL = @"libcrypto.so";
#else
        public const string DLL = @"libeay32.dll";
#endif
    }
    
    /* ---------------------------------------------------------------------- */
    public class EVPException : ApplicationException { };

    /* ---------------------------------------------------------------------- */
    unsafe struct EVP_MD_CTX { };
    unsafe struct EVP_MD { };

    public enum MDType
    {
        MD5, SHA1, SHA256, SHA384, SHA512
    }

    /* ---------------------------------------------------------------------- */
    internal sealed unsafe class _MD
    {
        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_MD_CTX* EVP_MD_CTX_create();

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern void EVP_MD_CTX_destroy(EVP_MD_CTX* handle);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_MD* EVP_MD_CTX_md(EVP_MD_CTX* handle);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_DigestInit_ex(EVP_MD_CTX* handle, EVP_MD* type, IntPtr engine);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_DigestUpdate(EVP_MD_CTX* handle, byte[] array, UIntPtr size);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_DigestFinal_ex(EVP_MD_CTX* handle, byte[] array, IntPtr psize);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_MD_block_size(EVP_MD* handle);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_MD_size(EVP_MD* handle);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_MD* EVP_md5();

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_MD* EVP_sha1();

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_MD* EVP_sha256();

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_MD* EVP_sha384();

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_MD* EVP_sha512();
    }

    /* ---------------------------------------------------------------------- */
#if !__MonoCS__
    [HostProtectionAttribute(MayLeakOnAbort=true)]
#endif
    public sealed unsafe class MD : IDisposable
    {
        private EVP_MD_CTX* _handle = null;
        private MDType _type;

        public void Dispose()
        {
            if (this._handle != null)
                _MD.EVP_MD_CTX_destroy(this._handle);
            this._handle = null;
        }

        internal static EVP_MD* GetMD(MDType type)
        {
            switch (type)
            {
                case MDType.MD5   : return _MD.EVP_md5   ();
                case MDType.SHA1  : return _MD.EVP_sha1  ();
                case MDType.SHA256: return _MD.EVP_sha256();
                case MDType.SHA384: return _MD.EVP_sha384();
                case MDType.SHA512: return _MD.EVP_sha512();
            }

            return null;
        }

        public MD(MDType type)
        {
            EVP_MD* md = null; // Statically allocated (MT), don't free
            EVP_MD_CTX* handle = null;

            if ((md = MD.GetMD(type)) == null)
                throw new EVPException();

            if ((handle = _MD.EVP_MD_CTX_create()) == null)
                goto Bailout;

            if (_MD.EVP_DigestInit_ex(handle, md, IntPtr.Zero) == 0)
                goto Bailout;

            this._handle = handle;
            this._type = type;
        
            return ;

        Bailout:
            if (handle != null)
                _MD.EVP_MD_CTX_destroy(handle);
            throw new EVPException();
        }

        public void Update(byte[] b)
        {
            _MD.EVP_DigestUpdate(this._handle, b, (UIntPtr)b.Length);
        }

        public byte[] Final()
        {
            byte[] data = new byte[this.Size];
            using (this)
            {
                _MD.EVP_DigestFinal_ex(this._handle, data, IntPtr.Zero);
                return data;
            }
        }

        public string Name
        {
            get { return Enum.GetName(typeof(MDType), this._type); }
        }

        public int BlockSize
        {
            get { return _MD.EVP_MD_block_size(_MD.EVP_MD_CTX_md(this._handle)); }
        }

        public int Size
        {
            get { return _MD.EVP_MD_size(_MD.EVP_MD_CTX_md(this._handle)); }
        }
    };

    /* ---------------------------------------------------------------------- */
    unsafe struct EVP_CIPHER_CTX { };
    unsafe struct EVP_CIPHER { };

    public enum CType
    {
        DES3, AES128, AES256
    }

    public enum CMode
    {
        ECB, CBC, GCM
    }

    /* ---------------------------------------------------------------------- */
    internal sealed unsafe class _CIPHER
    {
        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_CIPHER_CTX* EVP_CIPHER_CTX_new(); 

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern void EVP_CIPHER_CTX_init(EVP_CIPHER_CTX *handle); 

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern void EVP_CIPHER_CTX_free(EVP_CIPHER_CTX *handle); 

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern void EVP_CIPHER_CTX_cleanup(EVP_CIPHER_CTX *handle); 

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_CipherInit_ex(EVP_CIPHER_CTX *handle, EVP_CIPHER *cipher, IntPtr engine, byte[] key, byte[] iv, int enc);
        
        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_CIPHER_CTX_set_padding(EVP_CIPHER_CTX *handle, int padding);
        
        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_CIPHER_CTX_ctrl(EVP_CIPHER_CTX *handle, int type, int arg, byte[] ptr);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_CIPHER_CTX_ctrl(EVP_CIPHER_CTX *handle, int type, int arg, IntPtr ptr);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_CipherUpdate(EVP_CIPHER_CTX *handle, byte[] outbuf, ref int outlen, byte[] inbuf, int inlen);
        
        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_CipherFinal_ex(EVP_CIPHER_CTX *handle, byte[] outbuf, ref int outlen);
        
        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_CipherUpdate(EVP_CIPHER_CTX *handle, IntPtr outbuf, ref int outlen, IntPtr inbuf, int inlen);
        
        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_CipherFinal_ex(EVP_CIPHER_CTX *handle, IntPtr outbuf, ref int outlen);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_CIPHER* EVP_CIPHER_CTX_cipher(EVP_CIPHER_CTX *handle);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_CIPHER_CTX_block_size(EVP_CIPHER_CTX *handle);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_CIPHER_CTX_key_length(EVP_CIPHER_CTX *handle);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_CIPHER_CTX_set_key_length(EVP_CIPHER_CTX *handle, int length);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_CIPHER_CTX_iv_length(EVP_CIPHER_CTX *handle);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern int EVP_CIPHER_CTX_set_iv_length(EVP_CIPHER_CTX *handle, int length);

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_CIPHER* EVP_des_ede3();

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_CIPHER* EVP_des_ede3_cbc();

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_CIPHER* EVP_aes_128_ecb();

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_CIPHER* EVP_aes_128_cbc();

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_CIPHER* EVP_aes_128_gcm();

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_CIPHER* EVP_aes_256_ecb();

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_CIPHER* EVP_aes_256_cbc();

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_CIPHER* EVP_aes_256_gcm();

        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern EVP_CIPHER* EVP_rc4();
    }

    /* ---------------------------------------------------------------------- */
#if !__MonoCS__
    [HostProtectionAttribute(MayLeakOnAbort=true)]
#endif
    public sealed unsafe class CIPHER  : IDisposable
    {
        public const int EVP_CTRL_GCM_SET_IVLEN    = 0x09;
        public const int EVP_CTRL_GCM_GET_TAG      = 0x10;
        public const int EVP_CTRL_GCM_SET_TAG      = 0x11;
        public const int EVP_CTRL_GCM_SET_IV_FIXED = 0x12;
        public const int EVP_CTRL_GCM_SET_IV_GEN   = 0x13;

        private EVP_CIPHER_CTX* _handle = null;
        private CType  _type;
        private CMode  _mode;
        private bool   _encrypt;
        private byte[] _key;
        private byte[] _iv;

        private static Dictionary<Tuple<CType, CMode>, Func<IntPtr>> _ciphers;

        static CIPHER() {
            _ciphers = new Dictionary<Tuple<CType, CMode>, Func<IntPtr>>();

            _ciphers.Add(new Tuple<CType, CMode>(CType.DES3  , CMode.ECB), () => (IntPtr) _CIPHER.EVP_des_ede3());
            _ciphers.Add(new Tuple<CType, CMode>(CType.DES3  , CMode.CBC), () => (IntPtr) _CIPHER.EVP_des_ede3_cbc());
            _ciphers.Add(new Tuple<CType, CMode>(CType.AES128, CMode.ECB), () => (IntPtr) _CIPHER.EVP_aes_128_ecb());
            _ciphers.Add(new Tuple<CType, CMode>(CType.AES128, CMode.CBC), () => (IntPtr) _CIPHER.EVP_aes_128_cbc());
            _ciphers.Add(new Tuple<CType, CMode>(CType.AES128, CMode.GCM), () => (IntPtr) _CIPHER.EVP_aes_128_gcm());
            _ciphers.Add(new Tuple<CType, CMode>(CType.AES256, CMode.ECB), () => (IntPtr) _CIPHER.EVP_aes_256_ecb());
            _ciphers.Add(new Tuple<CType, CMode>(CType.AES256, CMode.CBC), () => (IntPtr) _CIPHER.EVP_aes_256_cbc());
            _ciphers.Add(new Tuple<CType, CMode>(CType.AES256, CMode.GCM), () => (IntPtr) _CIPHER.EVP_aes_256_gcm());
        }

        public void Dispose()
        {
            if (this._handle != null) {
                _CIPHER.EVP_CIPHER_CTX_cleanup(this._handle);
                _CIPHER.EVP_CIPHER_CTX_free(this._handle);
            }
            this._handle = null;
        }
        
        public CIPHER(CType type, CMode mode, bool encrypt)
        {
            EVP_CIPHER *cipher = null; // Statically allocated (MT), don't free
            EVP_CIPHER_CTX *handle = null;

            try {
                cipher = (EVP_CIPHER*) _ciphers[new Tuple<CType, CMode>(type, mode)]();
            } catch (KeyNotFoundException) {}

            if (cipher == null)
                goto Bailout;

            if ((handle = _CIPHER.EVP_CIPHER_CTX_new()) == null)
                goto Bailout;
            _CIPHER.EVP_CIPHER_CTX_init(handle);
            if (_CIPHER.EVP_CipherInit_ex(handle, cipher, IntPtr.Zero, null, null, encrypt ? 1 : 0) == 0)
                goto Bailout;
            _CIPHER.EVP_CIPHER_CTX_set_padding(handle, 0);

            this._handle  = handle;
            this._type    = type;
            this._mode    = mode;
            this._encrypt = encrypt;

            return ;

        Bailout:
            if (handle != null)
                _CIPHER.EVP_CIPHER_CTX_free(handle);
            throw new EVPException();
        }

        public CType type
        {
            get { return this._type; }
        }

        public CMode mode
        {
            get { return this._mode; }
        }

        public bool ForEncryption
        {
            get { return this._encrypt; }
        }

        public int KeyLength
        {
            get
            {
                return _CIPHER.EVP_CIPHER_CTX_key_length(this._handle);
            }

            set
            {
                if (_CIPHER.EVP_CIPHER_CTX_set_key_length(this._handle, value) == 0)
                    throw new EVPException();
            }
        }

        public byte[] Key
        {
            get { return this._key; }

            set
            {
                this.KeyLength = value.Length;
                if (_CIPHER.EVP_CipherInit_ex(this._handle, null, IntPtr.Zero, value, null, -1) == 0)
                    throw new EVPException();
                this._key = value;
            }
        }

        public int IVLength
        {
            get
            {
                return _CIPHER.EVP_CIPHER_CTX_iv_length(this._handle);
            }
        }

        public byte[] IV
        {
            get { return this._iv; }

            set
            {
                if (_CIPHER.EVP_CipherInit_ex(this._handle, null, IntPtr.Zero, null, value, -1) == 0)
                    throw new EVPException();
                this._iv = value;
            }
        }

        public int BlockSize
        {
            get
            {
                return _CIPHER.EVP_CIPHER_CTX_block_size(this._handle);
            }
        }

        public string Name
        {
            get { return Enum.GetName(typeof(CType), this._type); }
        }

        public int Process(byte[] ib, int ioff, int ilen, byte[] ob, int ooff)
        {
            int olen = 0;

            if (ib == null)
                throw new EVPException();
            if (ioff < 0 || ioff >= ib.Length)
                throw new EVPException();
            if (ib.Length - ioff < ilen)
                throw new EVPException();

            if (ob != null) {
                if (ooff < 0 || ooff >= ob.Length)
                    throw new EVPException();
                olen = ob.Length - ooff;
            } else
                ooff = 0;

            fixed (byte *obp = ob) {
            fixed (byte *ibp = ib) {
                IntPtr op = new IntPtr(obp + ooff);
                IntPtr ip = new IntPtr(ibp + ioff);

                if (_CIPHER.EVP_CipherUpdate(this._handle, op, ref olen, ip, ilen) == 0)
                    throw new EVPException();
            }
            }

            return olen;
        }

        public int Final(byte[] ob, int off)
        {
            int olen = 0;

            if (ob == null) {
                if (_CIPHER.EVP_CipherFinal_ex(this._handle, IntPtr.Zero, ref olen) == 0)
                    throw new EVPException();
                return olen;
            }

            if (ob != null) {
                if (off < 0 || off >= ob.Length)
                    throw new EVPException();
                olen = ob.Length - off;
            } else
                off = 0;

            fixed (byte *obp = ob) {
                IntPtr p = new IntPtr(obp + off);

                if (_CIPHER.EVP_CipherFinal_ex(this._handle, p, ref olen) == 0)
                    throw new EVPException();
            }

            return olen;
        }

        public void CTRL(int type, int arg, byte[] ptr, int offset)
        {
            if (ptr == null)
                offset = 0;

            fixed (byte *p = ptr) {
                IntPtr ip = new IntPtr(p + offset);

                if (_CIPHER.EVP_CIPHER_CTX_ctrl(this._handle, type, arg, ip) == 0)
                    throw new EVPException();
            }
        }
    }

    /* ---------------------------------------------------------------------- */
    public enum SType
    {
        RC4
    }

    /* ---------------------------------------------------------------------- */
#if !__MonoCS__
    [HostProtectionAttribute(MayLeakOnAbort=true)]
#endif
    public sealed unsafe class SCIPHER  : IDisposable
    {
        private EVP_CIPHER_CTX* _handle = null;
        private SType  _type;
        private bool   _encrypt;
        private byte[] _key;

        private static Dictionary<SType, Func<IntPtr>> _ciphers;

        static SCIPHER() {
            _ciphers = new Dictionary<SType, Func<IntPtr>>();
            _ciphers.Add(SType.RC4, () => (IntPtr) _CIPHER.EVP_rc4());
        }


        public void Dispose()
        {
            if (this._handle != null) {
                _CIPHER.EVP_CIPHER_CTX_cleanup(this._handle);
                _CIPHER.EVP_CIPHER_CTX_free(this._handle);
            }
            this._handle = null;
        }
        
        public SCIPHER(SType type, bool encrypt)
        {
            EVP_CIPHER *cipher = null; // Statically allocated (MT), don't free
            EVP_CIPHER_CTX *handle = null;

            try {
                cipher = (EVP_CIPHER*) _ciphers[type]();
            } catch (KeyNotFoundException) {}

            if (cipher == null)
                goto Bailout;

            if ((handle = _CIPHER.EVP_CIPHER_CTX_new()) == null)
                goto Bailout;
            _CIPHER.EVP_CIPHER_CTX_init(handle);
            if (_CIPHER.EVP_CipherInit_ex(handle, cipher, IntPtr.Zero, null, null, encrypt ? 1 : 0) == 0)
                goto Bailout;
            _CIPHER.EVP_CIPHER_CTX_set_padding(handle, 0);

            this._handle  = handle;
            this._type    = type;
            this._encrypt = encrypt;

            return ;

        Bailout:
            if (handle != null)
                _CIPHER.EVP_CIPHER_CTX_free(handle);
            throw new EVPException();
        }

        public SType type
        {
            get { return this._type; }
        }

        public bool ForEncryption
        {
            get { return this._encrypt; }
        }

        public int KeyLength
        {
            get
            {
                return _CIPHER.EVP_CIPHER_CTX_key_length(this._handle);
            }

            set
            {
                if (_CIPHER.EVP_CIPHER_CTX_set_key_length(this._handle, value) == 0)
                    throw new EVPException();
            }
        }

        public byte[] Key
        {
            get { return this._key; }

            set
            {
                this.KeyLength = value.Length;
                if (_CIPHER.EVP_CipherInit_ex(this._handle, null, IntPtr.Zero, value, null, -1) == 0)
                    throw new EVPException();
                this._key = value;
            }
        }

        public string Name
        {
            get { return Enum.GetName(typeof(CType), this._type); }
        }

        public byte[] Process(byte[] b)
        {
            byte[] aout   = new byte[b.Length];
            int    outlen = aout.Length;

            if (_CIPHER.EVP_CipherUpdate(this._handle, aout, ref outlen, b, b.Length) == 0)
                throw new EVPException();

            if (outlen != aout.Length)
                Array.Resize(ref aout, outlen);
            
            return aout;
        }
    }

    /* ---------------------------------------------------------------------- */
    internal sealed unsafe class _HMAC
    {
        [DllImport(Config.DLL, CharSet = CharSet.None, CallingConvention = CallingConvention.Cdecl)]
        public static extern IntPtr HMAC
            (EVP_MD *md, byte[] key, int klen, byte[] data, int len, byte[] aout, ref int olen); 
    }

    /* ---------------------------------------------------------------------- */
    public sealed unsafe class HMAC
    {
        private byte[]  _key;
        private MDType  _type;
        private EVP_MD *_md;

        
        public HMAC(MDType type)
        {
            this._type = type;
            this._md   = MD.GetMD(this._type);

            if (this._md == null)
                throw new EVPException();
        }

        public MDType type
        {
            get { return this._type; }
        }

        public byte[] Key
        {
            get { return this._key; }
            set { this._key = value; }
        }

        public string Name
        {
            get { return Enum.GetName(typeof(MDType), this._type); }
        }

        public byte[] HMac(byte[] b)
        {
            if (this._key == null)
                throw new EVPException();

            byte[] aout = new byte[_MD.EVP_MD_size(this._md)];
            int aoutlen = aout.Length;

            if (_HMAC.HMAC(this._md, this._key, this._key.Length, b, b.Length, aout, ref aoutlen) == IntPtr.Zero)
                throw new EVPException();
            if (aoutlen != aout.Length)
                throw new EVPException();
            return aout;
        }
    }
    
    /* ---------------------------------------------------------------------- */
    public class Core
    {
        [DllImport(Config.DLL, CharSet = CharSet.None)]
        public static extern int SSLeay();
    }
}
