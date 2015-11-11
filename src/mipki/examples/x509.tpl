sigAlg ::=
 seq {
   x: oid;
   defined by<x> {
    O1.2.840.113549.1.1.5:
     null
   };
  };

dirString ::=
 choice {
  x : teletex;
  x : printable;
  x : universal;
  x : utf8;
  x : bmp;
 };

RDN ::=
 set of<x> (1):
  seq {
   type : oid;
   $dirString<x=value>;
  };

x500 ::=
 # Can be empty
 seq of<x> (0):
  $RDN<x=attributes>;

generalName ::=
 choice {
  [1]* email : ascii;
  [2]* dns : ascii;
  [4]* $x500<x=dirName>;
  [6]* uri : ascii;
  [7]* ip : octet string;
  [8]* registeredID : oid;
 };

seq {

 # tbsCertificate
 seq {
  # Version
  [0] optional (0L) version : int [0L, 2L];

  # Serial Number
  serial : int;

  # Signature Algorithm
  $sigAlg<x=sigAlgOid>;

  # Issuer X500
  $x500<x=issuer>;

  # Validity Period
  seq {
   notBefore : utc date;
   notAfter  : utc date;
  };

  # Subject X500
  $x500<x=subject>;

  # Public Key
  seq {
   # Public Key Algorithm
   seq {
    publicKeyAlg : oid;
    defined by<publicKeyAlg> {
     default: null
    };
   };

   defined by<publicKeyAlg> {
    # RSA with PKCS#1
    O1.2.840.113549.1.1.1:
     bitstring:
      seq {
       modulus : int;
       exponent : int;
      }
   };
  };

  [3] optional defined by<version> {
   # Extensions may only appear in V3 certificate
   2L:
    seq of<extensions> (1):
     seq {
      extOid : oid;
      optional (false) extCritical : bool;
      defined by<extOid> {

       # Authority Information Access
       O1.3.6.1.5.5.7.1.1:
        octet string:
         seq of<authorityInformation> (1):
          seq {
           # Only allow OCSP and CA-issuer
           method : oid [O1.3.6.1.5.5.7.48.1, O1.3.6.1.5.5.7.48.2];
           choice {
            [4]* $x500<x=dirName>;
            [6]* uri : ascii;
           };
          }

       # Subject Key Identifier
       O2.5.29.14:
        octet string:
         subjectKeyIdentifier : octet string

       # Key Usage
       O2.5.29.15:
        octet string:
         keyUsage : bitstring

       # Subject Alternative Name
       O2.5.29.17:
        octet string:
         seq of<subjectAltNames> (1):
          $generalName

       # Basic Constraints
       O2.5.29.19:
        octet string:
         seq {
          optional (false) isCA : bool;
          optional pathLen : int;
         }

       # CRL Distribution Points
       O2.5.29.31:
        octet string:
         seq of<crlDistributionPoints> (1):
          seq {
           [0] optional choice {
             [0] choice {
              [4]* $x500<x=dirName>;
              [6]* uri : ascii;
             };
             [1] $RDN<x=relativetoCRLIssuer>;
            };
           [1] optional reasons : bitstring;
           [2] optional seq of<crlIssuer> (1):
            $generalName;
          }

       # Certificate Policies
       O2.5.29.32:
        octet string:
         seq of<policyInfo> (1):
          seq {
           policyId : oid;
           optional seq of<policyQualifiers> (1):
            seq {
             qualifierId : oid;
             defined by<qualifierId> {
              O1.3.6.1.5.5.7.2.1:
               policyURL : ascii
             };
            };
          }

       # Authority Key Identifier
       O2.5.29.35:
        octet string:
         seq {
          [0]* optional authorityKeyIdentifier : octet string;
          [1]* optional $x500<x=authorityIssuer>;
          [2]* optional authoritySerialNumber : int;
         }

       # Extended Key Usage
       O2.5.29.37:
        octet string:
         seq of<extendedKeyUsages> (1):
          eku : oid

       default:
        defined by<extCritical> {
         # Only allow non-critical unknown extensions
         false:
          extUnknown : octet string
        }
      };
     }
   };
 };
 # end tbsCertificate

 # Signature Algorithm
 $sigAlg<x=uSigAlg>;

 signature : bitstring;
}

