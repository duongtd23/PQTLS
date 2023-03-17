## Contents: In this folder, you can find:
- `hbtls-ca.cafe`: the specification of the protocol in case client authentication is requested. See the section below for a detailed explanation.
- `invariants.cafe`: all invariants/lemmas that are needed for the formal verification.
- others: proof scores, for example, `gen-pqKeySeAu.cafe` is the generated proof score for `pqKeySeAu`. Note that `forwardSe`, `ssKeySe`, `forwardSeAu`, `ssKeySeAu`, `inv7`, `inv8`, `inv15`, `inv23`, `inv34`, `inv35`, `inv40`, and `inv42` are proved without induction, but by using another invariants as lemmas.
- `inputs`: in case you want to re-generate the proof scores, this folder contains all input files that are necessary for that purpose. See README in the folder `without-client-authentication/inputs` for more detail.

## CafeOBJ specification with client authentication: a detail description
We first introduce the following module, where `intruder` and `ca` represent the intruder and the certificate authority:

```
mod* PRINCIPAL {
  [Prin]
  ops intruder ca : -> Prin {constr}
  eq (intruder = ca) = false .
}
```

The following two modules model long-term public and private keys:

```
mod! PUBLIC-KEY {
  pr(PRINCIPAL)
  [PubKey]
  op pubKey : Prin -> PubKey
  op owner : PubKey -> Prin
  vars A B : Prin 
  eq owner(pubKey(A)) = A .
  eq (pubKey(A) = pubKey(B)) = (A = B) .
}
mod! PRIVATE-KEY {
  pr(PRINCIPAL)
  [PriKey]
  op priKey : Prin -> PriKey 
  vars A B : Prin 
  eq (priKey(A) = priKey(B)) = (A = B) .
}
```

Next, we model random numbers, cipher suites, PQ KEMs parameters (), session IDs, protocol versions, and PQ KEM parameters used in the `ClientHello` message (note that comments in CafeOBJ are started with `--` and finished at the end of that line):

```
mod! RANDOM {
  [Rand]
}
mod! CIPHER-SUITE {
  [CipherSuite]
}
mod! PQ-KEM-PARAM {
  [PqKemParam]
-- for example, a PqKemParam can receive as value "KYBER-512-R3" - indicating that it supports Kyber with parameters defined in Kyber, the round 3 candidate to NIST PQC.
}
mod! SID {
  [Sid]
}
mod! PROTOCOL-VERSION {
  [Version]
}

-- for example: "KYBER-512-R3" - indicating that it supports KYBER with the parameters defined in the Kyber document specification
mod! PQ-KEM-PARAM {
  [PqKemParam]
}
```

We model the digital signature of principal `A` by `sign(CA,A,PK)`, where `CA` is the certificate authority signed the signature, and `PK` is the public key of `A`:
```
mod! SIGNATURE {
  pr(PRINCIPAL + PUBLIC-KEY + PRIVATE-KEY)
  [Sign]
  op sign    : Prin Prin PubKey -> Sign {constr}
  op signer  : Sign -> Prin
  op forwhom : Sign -> Prin
  op pubKey  : Sign -> PubKey
  var G : Sign
  vars A B A2 B2 : Prin
  vars PK PK2 : PubKey
  eq signer (sign(A,B,PK)) = A .
  eq forwhom(sign(A,B,PK)) = B .
  eq pubKey (sign(A,B,PK)) = PK .
  eq (sign(A,B,PK) = sign(A2,B2,PK2))
    = (A = A2 and B = B2 and PK = PK2) .
}
```

Certificates are then modeled as follows:
```
mod! CERTIFICATE {
  pr(SIGNATURE)
  [Cert]
  op cert   : Prin PubKey Sign -> Cert {constr}
  op owner  : Cert -> Prin
  op pubKey : Cert -> PubKey
  op sign   : Cert -> Sign
  vars A A2 : Prin
  vars PK PK2 : PubKey
  vars G G2 : Sign
  eq owner (cert(A,PK,G)) = A .
  eq pubKey(cert(A,PK,G)) = PK .
  eq sign  (cert(A,PK,G)) = G .
  eq (cert(A,PK,G) = cert(A2,PK2,G2)) 
    = (A = A2 and PK = PK2 and G = G2) .
}
```
For example, `cert(A,K,sign(CA,A,K))` denotes the certificate of principal `A` with its public key `K` signed by certificate authority `CA`.

Two modules `CERTIFICATE-TYPE` and `SIGNATURE-ALGORITHM` model two corresponding kinds of parameters sent in `CertificateRequest` messages:

```
mod! CERTIFICATE-TYPE {
  [CertType]
}
mod! SIGNATURE-ALGORITHM {
  [SignAlg]
}
```

We then model ECDH. Please check the paper for its description. Because we describe it in detail in the paper, we do not do it again here.
```
mod! CLASSICAL-KEY-EXCHANGE {
  [ClPriKeyEx ClPubKeyEx ClassicKey]
  op clPubKeyEx : ClPriKeyEx -> ClPubKeyEx {constr}
  op _&_ : ClPriKeyEx ClPriKeyEx -> ClassicKey {constr comm}
  op priClKey : ClPubKeyEx -> ClPriKeyEx
  op classicKey : ClPubKeyEx ClPriKeyEx -> ClassicKey
  ops $clKey1 $clKey2 : ClassicKey -> ClPriKeyEx
  vars K K2 K3 K4 : ClPriKeyEx
  vars PK PK2 : ClPubKeyEx
  var KC : ClassicKey
  eq priClKey(clPubKeyEx(K)) = K .
  eq clPubKeyEx(priClKey(PK)) = PK .
  eq (clPubKeyEx(K) = clPubKeyEx(K2)) = (K = K2) .
  eq classicKey(PK,K) = (priClKey(PK) & K) .
  eq $clKey1(K & K2) = K .
  eq $clKey2(K & K2) = K2 .
  eq ((K & K2) = (K3 & K4))
    = (K = K3 and K2 = K4) or
      (K = K4 and K2 = K3) .
}
```

Similarly, readers can check the paper for the description of PQ KEMs. Here we use an extended version of the NAT built-in module in CafeOBJ. The reason is because we need to define some extra (trivial) lemmas.
```
mod! NAT-EXTEND {
  pr(NAT)
  vars N N2 N3 : Nat .
  eq N > s(N) = false .
  ceq N2 > s(N) = false if N2 > N = false .
  op lm1 : Nat Nat Nat -> Bool
  eq lm1(N,N2,N3) = (N2 > N and not(N2 > N3))
    implies N3 > N .
}
mod! PQ-KEY-ENCAPSULATION {
  pr(NAT-EXTEND)
  [PqPriKey PqPubKey $PqKey PqKey PqCipher]
  op pqPubKeyEn : PqPriKey -> PqPubKey {constr}
  op _&_ : PqPriKey PqPriKey -> $PqKey {constr}
  op pqKey : $PqKey Nat -> PqKey {constr}
  op encapsCipher : PqPubKey PqPriKey -> PqCipher {constr}
  op encapsKey    : PqPubKey PqPriKey -> $PqKey
  op decaps : PqCipher PqPriKey -> $PqKey
  op priPqKey : PqPubKey -> PqPriKey
  op priPqKey : PqCipher -> PqPriKey
  ops $pqKey1 $pqKey2 : PqKey -> PqPriKey
  op time   : PqKey -> Nat
  vars K' K2' K3' K4' : PqPriKey
  vars PK' PK2' PK3' : PqPubKey
  var KP : PqKey
  vars KK KK2 : $PqKey
  vars N N2 : Nat
  var EN : PqCipher
  eq priPqKey(pqPubKeyEn(K')) = K' .
  eq pqPubKeyEn(priPqKey(PK')) = PK' .
  eq priPqKey(encapsCipher(PK', K2')) = K2' .
  eq (pqPubKeyEn(K') = pqPubKeyEn(K2')) = (K' = K2') .
  eq encapsKey(PK',K2') = (priPqKey(PK') & K2') .
  eq decaps(encapsCipher(pqPubKeyEn(K'), K2'), K') = (K' & K2') .
  eq $pqKey1(pqKey(K' & K2', N)) = K' .
  eq $pqKey2(pqKey(K' & K2', N)) = K2' .
  eq time(pqKey(K' & K2',N)) = N .
  eq (pqKey(KK, N) = pqKey(KK2, N2)) = (KK = KK2 and N = N2) .
  eq ((K' & K2') = (K3' & K4')) = (K' = K3' and K2' = K4') .
  eq (encapsCipher(PK', K2') = encapsCipher(PK3', K4')) =
    (PK' = PK3' and K2' = K4') .
  eq (decaps(EN,K') = (K3' & K2'))
    = (K3' = K' and EN = encapsCipher(pqPubKeyEn(K'), K2') ) .
}
```

We then model pre-master secrets:
```
mod! PRE-MASTER-SECRET {
  pr(CLASSICAL-KEY-EXCHANGE)
  pr(PQ-KEY-ENCAPSULATION)
  [Pms]
-- calculate the pre master secret by concatenating two shared keys
  op _||_ : ClassicKey PqKey -> Pms {constr}
  op pmsClKey : Pms -> ClassicKey
  op pmsPqKey : Pms -> PqKey
  op time : Pms -> Nat
  vars KC KC2 : ClassicKey 
  vars KP KP2 : PqKey 
  var PMS : Pms
  eq pmsClKey(KC || KP) = KC .
  eq pmsPqKey(KC || KP) = KP .
  eq time(PMS) = time(pmsPqKey(PMS)) .
  eq ((KC || KP) = (KC2 || KP2)) 
    = (KC = KC2 and KP = KP2) .
}
```

We then model seeds that used in the pseudo random function (PRF) functions. In the protocol, the PRF function is used for three kinds of purpose: (1) to compute master secrets from pre-master secrets, (2) to compute the handshake keys from master secrets, and (3) to compute the verify_data field values. 
For the three purposes, different labels are used resulting in different output values. 
Therefore, we introduce several separate PRF functions. 
`prf-ms` is used for (1), while `prf-ckey` and `prf-skey` are used for (2). 
Note that "client finished" is used for the seed field when compute the symmetric handshake key for the client side, while "server finished" is used for the server side, so they can be separated. 
The seed field for `prf-ckey` and `prf-skey` is the two random numbers (in Hello messages), and is modeled by `seedHs` operator. 
While for `prf-ms`, we need the two ECDHE public key and the PQ KEM ciphertext in addition, and is modeled by `seedMs` operator. We introduce the two modules as follows:
<!--  including (i) `prf-ms`, (ii) `prf-ckey` and (iii) `prf-skey` (note that `client finished` is used for the seed field when compute the symmetric handshake key for the client side, while `server finished` is used for the server side, so although (ii) and (iii) belong to (2), they can be separated), and (iv) `prf-sfin`. -->
```
mod! PRF-SEED {
  pr(PRE-MASTER-SECRET + RANDOM)
  [Seed]
  op seedHs : Rand Rand -> Seed {constr}
  op seedMs : Rand Rand ClPubKeyEx PqCipher -> Seed {constr}
  vars R R2 R' R2' : Rand
  vars PK PK2 : ClPubKeyEx 
  vars PK' PK2' : PqPubKey 
  vars EN EN2 : PqCipher
  eq (seedHs(R,R2) = seedHs(R',R2')) 
    = (R = R' and R2 = R2') .
  eq (seedMs(R,R2,PK,EN) = seedMs(R',R2',PK2,EN2)) 
    = (R = R' and R2 = R2' and PK = PK2 and EN = EN2) .
}
mod! MASTER-SECRET {
  pr(PRF-SEED)
  [Ms]
  op prf-ms : Pms Seed -> Ms {constr} .
  op getPms : Ms -> Pms
  op time : Ms -> Nat
  vars PMS PMS2 : Pms
  vars SD SD2 : Seed
  var MS : Ms
  eq getPms(prf-ms(PMS,SD)) = PMS .
  eq time(MS) = time(getPms(MS)) .
  eq (prf-ms(PMS,SD) = prf-ms(PMS2,SD2)) =
    (PMS = PMS2 and SD = SD2) .
}
```

Similaryly, we model handshake keys:
```
mod! HANDSHAKE-KEY {
  pr(MASTER-SECRET + PRIVATE-KEY + PUBLIC-KEY)
  [Key]
  vars A B : Prin
  vars K K2 : ClPriKeyEx
  vars R R2 R3 R4 : Rand
  vars MS MS2 : Ms
  vars PK PK2 : ClPubKeyEx
  vars PK' PK2' : PqPubKey
  vars SD SD2 : Seed
  vars HSK : Key 
  op prf-ckey : Ms Seed -> Key {constr} .
  op prf-skey : Ms Seed -> Key {constr} .
  op getMs : Key -> Ms
  eq (prf-ckey(MS,SD) = prf-ckey(MS2,SD2)) =
    (MS = MS2 and SD = SD2) .
  eq (prf-skey(MS,SD) = prf-skey(MS2,SD2)) =
    (MS = MS2 and SD = SD2) .
  eq getMs(prf-ckey(MS,SD)) = MS .
  eq getMs(prf-skey(MS,SD2)) = MS .
  op time : Key -> Nat
  eq time(HSK) = time(getMs(HSK)) .
}
```

Sort `Cipher`, `Hash`, and `FinVD` represent ciphertexts, hashs, and verify_datas. 
Because different labels are used for the PRF function when compute the verify_data for a client's `Finished` message and a server's `Finished` message, we separately define two PRF functions `prf-cfin` and `prf-sfin`. Similarly, we define `prf-cfin2` and `prf-sfin2` for the abbreviated handshake mode.
For `Hash`, similarly, we define three constructors for it including `hFullHs`, `hAbbrHs`, and `hParams`, representing the calculations of hash of all handshake messages in the full handshake mode, and hash of all handshake messages in the abbreviated handshake mode, and hash of the two random numbers and the client's ECDHE public key and PQ KEM ciphertext (used in the `ServerKeyExchange` message).
```
mod! LIST(D :: TRIV) {
  [Elt.D < List]
  op _\in_ : Elt.D List -> Bool 
}
view TRIV2CIPHER-SUITE from TRIV to CIPHER-SUITE {
  sort Elt -> CipherSuite
}
view TRIV2PQ-KEM-PARAM from TRIV to PQ-KEM-PARAM {
  sort Elt -> PqKemParam
}
view TRIV2CERTTYPE from TRIV to CERTIFICATE-TYPE {
  sort Elt -> CertType
}
view TRIV2SIGNALG from TRIV to SIGNATURE-ALGORITHM {
  sort Elt -> SignAlg
}
mod! ENCRYPTION {
  pr(HANDSHAKE-KEY + CERTIFICATE + SID + PROTOCOL-VERSION)
  pr(LIST(D <= TRIV2CIPHER-SUITE)*{sort List -> CipherSuites})
  pr(LIST(D <= TRIV2PQ-KEM-PARAM)*{sort List -> PqKemParams})
  pr(LIST(D <= TRIV2CERTTYPE)*{sort List -> CertTypes})
  pr(LIST(D <= TRIV2SIGNALG)*{sort List -> SignAlgs})
  [Cipher] [Hash] [FinVD]

-- for verify_datas
  op prf-cfin  : Ms Hash -> FinVD {constr}
  op prf-sfin  : Ms Hash -> FinVD {constr}
  op prf-cfin2 : Ms Hash -> FinVD {constr}
  op prf-sfin2 : Ms Hash -> FinVD {constr}

-- for hash functions
  op hFullHs : Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid
    Cert
    ClPubKeyEx PqPubKey Cipher
    CertTypes SignAlgs
    Cert
    ClPubKeyEx PqCipher -> Hash {constr}
  op hAbbrHs : Prin Prin Version Rand Sid CipherSuites
    Rand CipherSuite -> Hash {constr}
  op hParams : Rand Rand ClPubKeyEx PqPubKey -> Hash {constr}

-- for encryption
  op encFin : Key FinVD   -> Cipher {constr}
  op encH   : PriKey Hash -> Cipher {constr}

-- decryption using symetric key
  op decSym? : Cipher Key -> Bool
  op decFin  : Cipher Key -> FinVD
  eq decSym?(encFin(KR,FVD),KR2) = (KR = KR2) .
  ceq decFin(encFin(KR,FVD),KR2) = FVD if decSym?(encFin(KR,FVD),KR2) .

-- decryption using asymetric key
  op decAsym? : Cipher PubKey -> Bool
  op decH     : Cipher PubKey -> Hash
  eq decAsym?(encH(priKey(A), H), PKE) = (PKE = pubKey(A)) .
  ceq decH(encH(KE, H), PKE) = H if decAsym?(encH(KE, H), PKE) .

  vars CI CI2 : Cipher
  vars PK PK2 PK3 PK4 : ClPubKeyEx
  vars PK' PK2' PK3' PK4' : PqPubKey
  vars KE KE2 : PriKey
  vars PKE PKE2 : PubKey 
  vars MS MS2 : Ms
  vars KR KR2 : Key 
  vars H H2 : Hash
  vars A B A2 B2 : Prin
  vars R R2 R3 R4 : Rand
  vars CSs CSs2 : CipherSuites
  vars CS CS2 : CipherSuite
  vars I I2 : Sid
  vars CERT CERT2 CERT3 CERT4 : Cert 
  vars KEMs KEMs2 : PqKemParams
  vars FVD FVD' FVD2 : FinVD
  vars V V2 : Version
  vars EN EN2 : PqCipher
  vars CRTs CRTs2 : CertTypes
  vars SGAs SGAs2 : SignAlgs

  eq (hFullHs(A,B,V,R,CSs,KEMs,R2,CS,I,CERT,PK,PK',CI,CRTs,SGAs,CERT3,PK2,EN) =
      hFullHs(A2,B2,V2,R3,CSs2,KEMs2,R4,CS2,I2,CERT2,PK3,PK3',CI2,CRTs2,SGAs2,CERT4,PK4,EN2)) =
    (A = A2 and B = B2 and R = R3 and CSs = CSs2 and 
     KEMs = KEMs2 and R2 = R4 and CS = CS2 and I = I2 and 
     CERT = CERT2 and PK = PK3 and PK' = PK3' and 
     CI = CI2 and PK2 = PK4 and EN = EN2 and V = V2 and
     CRTs = CRTs2 and SGAs = SGAs2 and CERT3 = CERT4) .   
  eq (hAbbrHs(A,B,V,R,I,CSs,R2,CS) =
      hAbbrHs(A2,B2,V2,R3,I2,CSs2,R4,CS2)) =
    (A = A2 and B = B2 and R = R3 and CSs = CSs2 and 
     R2 = R4 and CS = CS2 and I = I2 and V = V2) . 
  eq (hParams(R,R2,PK,PK') = hParams(R3,R4,PK2,PK2')) =
    (R = R3 and R2 = R4 and PK = PK2 and PK' = PK2') .
  eq (hFullHs(A,B,V,R,CSs,KEMs,R2,CS,I,CERT,PK,PK',CI,CRTs,SGAs,CERT3,PK2,EN) =
    hAbbrHs(A2,B2,V2,R3,I2,CSs2,R4,CS2)) = false .
  eq (hFullHs(A,B,V,R,CSs,KEMs,R2,CS,I,CERT,PK,PK',CI,CRTs,SGAs,CERT3,PK2,EN) =
    hParams(R3,R4,PK3,PK3')) = false .
  eq (hAbbrHs(A,B,V,R,I,CSs,R2,CS) = hParams(R3,R4,PK3,PK3')) = false .
  eq (encH(KE, H) = encH(KE2, H2)) = (KE = KE2 and H = H2) .
  eq (encFin(KR,FVD) = encFin(KR2,FVD2)) = (KR = KR2 and FVD = FVD2) .  
  eq (prf-cfin(MS,H) = prf-cfin(MS2,H2)) = (MS = MS2 and H = H2) .
  eq (prf-sfin(MS,H) = prf-sfin(MS2,H2)) = (MS = MS2 and H = H2) .
  eq (prf-cfin2(MS,H) = prf-cfin2(MS2,H2)) = (MS = MS2 and H = H2) .
  eq (prf-sfin2(MS,H) = prf-sfin2(MS2,H2)) = (MS = MS2 and H = H2) .
  op getClientClKEx : Hash -> ClPubKeyEx
  op getClientPqCiph : Hash -> PqCipher
  eq getClientClKEx(hFullHs(A,B,V,R,CSs,KEMs,R2,CS,I,CERT,PK,PK',CI,CRTs,SGAs,CERT3,PK2,EN))
    = PK2 .
  eq getClientPqCiph(hFullHs(A,B,V,R,CSs,KEMs,R2,CS,I,CERT,PK,PK',CI,CRTs,SGAs,CERT3,PK2,EN))
    = EN .
}
```
<!-- Note that -->

We then introduce module `MESSAGE` modeling messages exchanged in the protocol. The module first declares sort `Msg` with 17 constructors where their explanations are given in the code comments:
```
mod! MESSAGE {
  pr(ENCRYPTION)
  [Msg]

-- client hello, server hello messages (for the full handshake)
  op chM : Prin Prin Prin Version Rand CipherSuites PqKemParams -> Msg {constr}
  op shM : Prin Prin Prin Version Rand CipherSuite Sid -> Msg {constr}

-- server certificate message
  op scertM : Prin Prin Prin Cert -> Msg {constr}

-- client key exchange, server key exchange messages
  op skexM : Prin Prin Prin ClPubKeyEx PqPubKey Cipher Nat -> Msg {constr}
  op ckexM : Prin Prin Prin ClPubKeyEx PqCipher Nat -> Msg {constr}

-- server hello done
  op shDnM : Prin Prin Prin -> Msg {constr}
-- change cipher spec
  op ccsM : Prin Prin Prin -> Msg {constr}

-- client authentication messages, certificate request
  op certReqM : Prin Prin Prin CertTypes SignAlgs -> Msg {constr}

-- client certificate
  op ccertM : Prin Prin Prin Cert -> Msg {constr}

-- certificate verify
  op certVerM : Prin Prin Prin Cipher -> Msg {constr}

-- client finished, server finished messages (for the full handshake)
  op cfM : Prin Prin Prin Cipher -> Msg {constr}
  op sfM : Prin Prin Prin Cipher -> Msg {constr}

-- client hello 2, server hello 2 (for the abbreviated handshake, session resumption)
  op ch2M : Prin Prin Prin Version Rand Sid CipherSuites -> Msg {constr}
  op sh2M : Prin Prin Prin Version Rand Sid CipherSuite -> Msg {constr}

-- client finished 2, server finished 2 (for the abbreviated handshake, session resumption)
  op sf2M : Prin Prin Prin Cipher -> Msg {constr}
  op cf2M : Prin Prin Prin Cipher -> Msg {constr}

-- hello request, an optional message sent from server to client
  op heReM : Prin Prin Prin -> Msg {constr}
```

The module then declares some predicates `x?` checking a given message is a `x` message:
```
  op chM?    : Msg -> Bool
  op shM?    : Msg -> Bool
  op scertM? : Msg -> Bool
  op skexM?  : Msg -> Bool
  op ckexM?  : Msg -> Bool
  op cfM?    : Msg -> Bool
  op sfM?    : Msg -> Bool
  op ch2M?   : Msg -> Bool
  op sh2M?   : Msg -> Bool
  op cf2M?   : Msg -> Bool
  op sf2M?   : Msg -> Bool
  op ccertM? : Msg -> Bool
  op certVerM? : Msg -> Bool
```
For example, `chM?` checks if a given message is a `ClientHello` message.

The module then declares some projection operators:
```
  op crt : Msg -> Prin   -- get creator of the message
  op src : Msg -> Prin   -- get sender of the message
  op dst : Msg -> Prin   -- get receiver of the message
  
  op getCS       : Msg -> CipherSuites
  op getClKey    : Msg -> ClPubKeyEx
  op getPqKey    : Msg -> PqPubKey
  op getRand     : Msg -> Rand
  op getCipher   : Msg -> Cipher
  op getCert     : Msg -> Cert
  op time        : Msg -> Nat
  op getPqCipher : Msg -> PqCipher
```

The equations in this module are not hard to comprehend, so we do not explain.

We then define three abstract kinds of data structures (they will be instantiated with some parameters later to derive some concrete data structures).
```
mod! BAG (D :: TRIV) {
  [Elt.D < Bag]
  op void : -> Bag {constr}
  op _,_ : Bag Bag -> Bag {assoc constr comm id: void}
  op _\in_ : Elt.D Bag -> Bool
  var B : Bag
  vars E1 E2 : Elt.D
  eq E1 \in void = false .
  eq E1 \in E2 = (E1 = E2) .
  eq E1 \in (E2,B) = (E1 = E2) or (E1 \in B) .
}
mod! SET (D :: TRIV) {
  [Elt.D < Set]
  op empty : -> Set {constr}
  op __ : Set Set -> Set {assoc constr comm idem id: empty}
  op _\in_ : Elt.D Set -> Bool
  var S : Set
  vars E1 E2 : Elt.D
  eq E1 \in empty = false .
  eq E1 \in E2 = (E1 = E2) .
  eq E1 \in (E2 S) = (E1 = E2) or (E1 \in S) .
}
mod! COLLECTION(D :: TRIV) {
  [Elt.D < Col]
  op _\in_ : Elt.D Col -> Bool 
}
```

We then model the network:
```
view TRIV2SIGN from TRIV to SIGNATURE {
  sort Elt -> Sign
}
view TRIV2MESSAGE from TRIV to MESSAGE {
  sort Elt -> Msg
}
view TRIV2CIPHER from TRIV to ENCRYPTION {
  sort Elt -> Cipher
}
mod! NETWORK {
  pr(HANDSHAKE-KEY)
  pr(BAG(D <= TRIV2MESSAGE)*{sort Bag -> Network})
  pr(COLLECTION(D <= TRIV2CIPHER)*{sort Col -> ColEnc})
  pr(COLLECTION(D <= TRIV2SIGN)*{sort Col -> ColSign})

-- collection of signatures gleaned by the intruder
  op csign : Network -> ColSign

  vars NW NW10 : Network
  vars M M2 : Msg
  var G : Sign
  vars KC KC2 : ClassicKey 
  vars KP KP2 : PqKey 

  eq G \in csign(void) = false .
  eq G \in csign(M,NW) 
    = (scertM?(M) and G = sign(getCert(M)))
    or G \in csign(NW) .
```

`csign(NW)` denotes the collection of signatures gleaned by the intruder from the network `NW`. The two equations defining it say that the intruder can grasp a signature from a `Certificate` message when that message exists in the network.

The module then defines two important predicates, namely `existClPriKexM` and `existPqPriKexM`.
`existPqPriKexM(KP,NW)` whether there exists a `ServerKeyExchange` or a `ClientKeyExchange` message in the network `NW` such that one of the two secret keys of `KP` equals the secret key associated with the PQ KEM public key sent in that message and intruder is the actual creator of that message (only in that case, the intruder owns the secret key). If that is the case, the intruder can derive the PQ KEM shared secret because the public part of `KP` can be easily grasped be everyone since it is sent in plaintext.
For `existClPriKexM`, it is defined simpler since we suppose that the intruder can break the security of ECDH, i.e., the intruder can derive the ECDH shared secret once he/she grasps the corresponding two ECDHE public key exchanged between client and server.
<!-- `existClPriKexM(KC,NW)` checks whether there exists a `ServerKeyExchange` or a `ClientKeyExchange` message in the network `NW` such that one of the two secret keys of `KC` equals the secret key associated with the ECDHE public key sent in that message and intruder is the actual creator of that message (only in that case, the intruder owns the secret key) -->

```
  op existClPriKexM : ClassicKey Network -> Bool .
  op existPqPriKexM : PqKey Network -> Bool .
  eq existClPriKexM(KC, void) = false . 
  eq existClPriKexM(KC, (M,NW))
    = ((ckexM?(M) or skexM?(M)) and
       (priClKey(getClKey(M)) = $clKey1(KC) or
        priClKey(getClKey(M)) = $clKey2(KC)))
      or existClPriKexM(KC, NW) .
  eq existPqPriKexM(KP, void) = false . 
  eq existPqPriKexM(KP, (M,NW))
    = (((skexM?(M) and
        (priPqKey(getPqKey(M)) = $pqKey1(KP) or
         priPqKey(getPqKey(M)) = $pqKey2(KP))) or
       (ckexM?(M) and 
        (priPqKey(getPqCipher(M)) = $pqKey1(KP) or
         priPqKey(getPqCipher(M)) = $pqKey2(KP)))) and 
       crt(M) = intruder and time(M) = time(KP))
      or existPqPriKexM(KP, NW) .
}
```

We next introduce the following module:

```
mod! SESSION-STATE {
  pr(HANDSHAKE-KEY + SID + CIPHER-SUITE)
  [Session]
  op none : -> Session {constr}
  op session : Sid CipherSuite Ms -> Session {constr}
  op sid : Session -> Sid
  op cs : Session -> CipherSuite
  op ms : Session -> Ms
  var S : Session 
  vars I I2 : Sid 
  vars CS CS2 : CipherSuite
  vars MS MS2 : Ms
  eq sid(session(I,CS,MS)) = I .
  eq cs(session(I,CS,MS)) = CS .
  eq ms(session(I,CS,MS)) = MS .
  eq (session(I,CS,MS) = session(I2,CS2,MS2))
     = (I = I2 and CS = CS2 and MS = MS2) .
}
```
`session(I,CS,MS)` saves the session information (including the selected cipher suite and the master secret) once client & server complete a full handshake. That information will be used later for the session resumption.

Next, for modeling the long-term private keys compromise, we first introduce the following module:
```
mod! PRIKEY-TIME {
  pr(PRIVATE-KEY + NAT-EXTEND)
  [PriKeyTime]
  op pkNPair : PriKey Nat -> PriKeyTime {constr}
  op getPriK : PriKeyTime -> PriKey
  op getTime : PriKeyTime -> Nat
  vars N N2 : Nat
  vars KE KE2 : PriKey
  eq getPriK(pkNPair(KE, N)) = KE .
  eq getTime(pkNPair(KE, N)) = N .
  eq (pkNPair(KE, N) = pkNPair(KE2, N2))
    = (KE = KE2 and N = N2) .
}
```
`pkNPair(KE,N)` denotes a pair of the long-term private key `KE` and the time `N`, where `N` is the time when `KE` is compromised.

We then define a set of long-term private keys compromised with the operator `_\in'_`, a predicate checking whether a given long-term private key exists in the set of compromised keys.
```
view TRIV2PRIKEYTIME from TRIV to PRIKEY-TIME {
  sort Elt -> PriKeyTime
}
mod PRIKEY-TIME-SET {
  pr(SET(D <= TRIV2PRIKEYTIME)*{sort Set -> PriKeyTimeS})
  
  op _\in'_ : PriKey PriKeyTimeS -> Bool .
  op timeLeak : PriKey PriKeyTimeS -> Nat .

  var KES : PriKeyTimeS
  var KET : PriKeyTime
  vars KE1 KE2 : PriKey
  vars N N2 : Nat 
  eq KE1 \in' empty = false .
  eq KE1 \in' (KET KES) = (KE1 = getPriK(KET)) or (KE1 \in' KES) .

  eq timeLeak(KE1, empty) = 0 .
  eq timeLeak(KE1, (KET KES)) = 
    (if (KE1 = getPriK(KET))
     then getTime(KET)
     else timeLeak(KE1, KES)
     fi) .
}
```

Now, we are ready to model the protocol execution. Sort `Sys` is introduced denoting the state space.
The module declares transitions for the full handshake mode:
```
view TRIV2PMS from TRIV to PRE-MASTER-SECRET {
  sort Elt -> Pms
}
view TRIV2CLPRIKEYEX from TRIV to CLASSICAL-KEY-EXCHANGE {
  sort Elt -> ClPriKeyEx
}
view TRIV2PQPRIKEYEN from TRIV to PQ-KEY-ENCAPSULATION {
  sort Elt -> PqPriKey
}
view TRIV2KEYEX from TRIV to HANDSHAKE-KEY {
  sort Elt -> Key
}
view TRIV2CLKEYEX from TRIV to CLASSICAL-KEY-EXCHANGE {
  sort Elt -> ClassicKey
}
view TRIV2PQKEYEN from TRIV to PQ-KEY-ENCAPSULATION {
  sort Elt -> PqKey
}
mod HB-TLS12 {
  pr(NETWORK + SESSION-STATE)
  pr(SET(D <= TRIV2RANDOM)*{sort Set -> URand})
  pr(SET(D <= TRIV2SID)*{sort Set -> USid})
  pr(SET(D <= TRIV2CLPRIKEYEX)*{sort Set -> ClPriKeyExS})
  pr(SET(D <= TRIV2PQPRIKEYEN)*{sort Set -> PqPriKeyS})
  pr(COLLECTION(D <= TRIV2PMS)*{sort Col -> ColPms})
  pr(SET(D <= TRIV2KEYEX)*{sort Set -> KeyS})
  pr(COLLECTION(D <= TRIV2KEYEX)*{sort Col -> ColHsK})
  pr(COLLECTION(D <= TRIV2CLKEYEX)*{sort Col -> ColClKey})
  pr(COLLECTION(D <= TRIV2PQKEYEN)*{sort Col -> ColPqKey})
  pr(PRIKEY-TIME-SET)

  [Sys]

-- an arbitrary initial state is represented by init
  op init : -> Sys {constr}

-- transitions for the full handshake
-- sending client hello 
  op chello : Sys Prin Prin Version Rand CipherSuites 
    PqKemParams -> Sys {constr}
-- sending server hello 
  op shello : Sys Rand CipherSuite Sid
    Prin Prin Prin Version Rand CipherSuites PqKemParams -> Sys {constr}
-- sending server certificate 
  op scert : Sys
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid -> Sys {constr}
-- sending server key exchange 
  op skeyex : Sys ClPriKeyEx PqPriKey
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid -> Sys {constr}
-- sending certification request 
  op certReq : Sys CertTypes SignAlgs 
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid 
    ClPriKeyEx PqPriKey Nat -> Sys {constr}
-- sending server hello done 
  op shelloDone : Sys 
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid 
    ClPriKeyEx PqPriKey Nat -> Sys {constr}
-- sending client certificate
  op ccert : Sys
    Prin Prin Version Rand CipherSuites PqKemParams
    Prin Rand CipherSuite Sid 
    Cert
    ClPubKeyEx PqPubKey Cipher Nat
    CertTypes SignAlgs -> Sys {constr}
-- sending client key exchange 
  op ckeyex : Sys ClPriKeyEx PqPriKey
    Prin Prin Version Rand CipherSuites PqKemParams
    Prin Rand CipherSuite Sid 
    Cert
    ClPubKeyEx PqPubKey Cipher Nat 
    CertTypes SignAlgs -> Sys {constr}
-- sending certificate verify
  op certVerify : Sys
    Prin Prin Version Rand CipherSuites PqKemParams
    Prin Rand CipherSuite Sid 
    Cert
    ClPubKeyEx PqPubKey Cipher Nat
    CertTypes SignAlgs
    ClPriKeyEx PqPriKey Nat -> Sys {constr}
-- sending client change cipher spec
  op cChangeCS : Sys
    Prin Prin Version Rand CipherSuites PqKemParams
    Prin Rand CipherSuite Sid 
    Cert
    ClPubKeyEx PqPubKey Cipher Nat 
    CertTypes SignAlgs
    ClPriKeyEx PqPriKey Nat -> Sys {constr}
-- sending client finished
  op cfinish : Sys 
    Prin Prin Version Rand CipherSuites PqKemParams
    Prin Rand CipherSuite Sid
    Cert
    ClPubKeyEx PqPubKey Cipher Nat 
    CertTypes SignAlgs
    ClPriKeyEx PqPriKey Nat -> Sys {constr}
-- sending server change cipher spec
  op sChangeCS : Sys
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid
    ClPriKeyEx PqPriKey Nat
    CertTypes SignAlgs
    Prin Cert
    ClPubKeyEx PqCipher Nat
    Cipher -> Sys {constr}
-- sending server finished
  op sfinish : Sys 
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid
    ClPriKeyEx PqPriKey Nat
    CertTypes SignAlgs
    Prin Cert
    ClPubKeyEx PqCipher Nat
    Cipher -> Sys {constr}
```

The module then declares transitions for the abbreviated handshake and for sending server hello request messages:
```
-- transitions for session resumption / abbreviated handshake
-- sending client hello 
  op chello2 : Sys Prin Prin Version Rand Sid CipherSuites 
    -> Sys {constr}
-- sending server hello 
  op shello2 : Sys Rand
    Prin Prin Prin Version Rand Sid CipherSuites -> Sys {constr}
-- sending server change cipher spec
  op sChangeCS2 : Sys
    Prin Prin Prin Version Rand Sid CipherSuites 
    Rand -> Sys {constr}
-- sending server finished
  op sfinish2 : Sys
    Prin Prin Prin Version Rand Sid CipherSuites 
    Rand -> Sys {constr}
-- sending client change cipher spec
  op cChangeCS2 : Sys
    Prin Prin Version Rand Sid CipherSuites 
    Prin Rand 
    Prin
    Prin -> Sys {constr}
-- sending client finished
  op cfinish2 : Sys
    Prin Prin Version Rand Sid CipherSuites 
    Prin Rand 
    Prin
    Prin -> Sys {constr}

-- sending server hello request (before client hello)
  op helloReq : Sys Prin Prin -> Sys {constr}
```

Then, transitions for the intruder capabilities are declared as follows:
```
-- intruder capabilities
-- faking client hello
  op fkChello : Sys Prin Prin Version Rand CipherSuites PqKemParams -> Sys {constr}
-- faking server hello
  op fkShello : Sys Prin Prin Version Rand CipherSuite Sid -> Sys {constr}
-- faking server certificate
  op fkCert : Sys Prin Prin PubKey Sign -> Sys {constr}
-- faking server key exchange (2 transitions)
  op fkSkeyex : Sys Prin Prin ClPriKeyEx PqPriKey Rand Rand -> Sys {constr}
  op fkSkeyex2 : Sys Prin Prin ClPriKeyEx PqPriKey Rand Rand -> Sys {constr}
-- faking server hello done 
  op fkShelloDone : Sys Prin Prin -> Sys {constr}
-- faking client key exchange (2 transitions)
  op fkCkeyex : Sys Prin Prin ClPriKeyEx PqPriKey PqPubKey -> Sys {constr}
  op fkCkeyex2 : Sys Prin Prin ClPriKeyEx PqPriKey PqPubKey -> Sys {constr}
-- faking client finished
  op fkCfinish : Sys Pms PubKey Sign PubKey Sign
    Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid
    ClPubKeyEx PqPubKey Cipher
    ClPubKeyEx PqCipher 
    CertTypes SignAlgs -> Sys {constr}
-- faking server finished
  op fkSfinish : Sys Pms PubKey Sign PubKey Sign
    Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid
    ClPubKeyEx PqPubKey Cipher
    ClPubKeyEx PqCipher 
    CertTypes SignAlgs -> Sys {constr}
-- faking cerificate request
  op fkCertReq : Sys Prin Prin CertTypes SignAlgs -> Sys {constr}
-- faking client cerificate
  op fkCCert : Sys Prin Prin PubKey Sign -> Sys {constr}
-- faking cerificate verify
  op fkCertVerify : Sys PubKey Sign PubKey Sign
    Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid
    ClPubKeyEx PqPubKey Cipher
    ClPubKeyEx PqCipher 
    CertTypes SignAlgs -> Sys {constr}
-- faking client hello 2
  op fkChello2 : Sys Prin Prin Version Rand Sid CipherSuites -> Sys {constr}
-- faking server hello 2
  op fkShello2 : Sys Prin Prin Version Rand Sid CipherSuite -> Sys {constr}
-- faking client finished 2
  op fkCfinish2 : Sys Prin Prin Version Rand Sid CipherSuites 
    Rand Pms CipherSuite ClPubKeyEx PqCipher -> Sys {constr}
-- faking server finished 2
  op fkSfinish2 : Sys Prin Prin Version Rand Sid CipherSuites 
    Rand Pms CipherSuite ClPubKeyEx PqCipher -> Sys {constr}
-- faking change cipher spec
  op fkChangeCS : Sys Prin Prin -> Sys {constr}
```

Secret keys compromised are modeled by the following transitions:
```
-- ECDH and PQ KEM keys compromise
  op leakPKE1 : Sys Prin Prin Prin ClPubKeyEx PqPubKey Cipher Nat -> Sys {constr}
  op leakPKE2 : Sys Prin Prin Prin ClPubKeyEx PqPubKey Cipher Nat -> Sys {constr}
  op leakPKE3 : Sys Prin Prin Prin ClPubKeyEx PqCipher Nat -> Sys {constr}
  op leakPKE4 : Sys Prin Prin Prin ClPubKeyEx PqCipher Nat -> Sys {constr}
-- handshake keys compromise
  op leakHsK : Sys Prin Prin Key FinVD -> Sys {constr}
-- long-term private keys compromise
  op leakLtK : Sys Prin -> Sys {constr}
```

We use the following observers:
```
-- the network
  op nw : Sys -> Network
-- the set of used random numbers
  op ur : Sys -> URand
-- the set of used session IDs
  op ui : Sys -> USid
-- the set of used ECDHE secret keys
  op uclk : Sys -> ClPriKeyExS
-- and the set of used PQ KEM secret keys
  op upqk : Sys -> PqPriKeyS
-- session state between two principals
  op ss : Sys Prin Prin Sid -> Session
-- compromised ECDHE ephemeral secret keys set
  op clkLeaked : Sys -> ClPriKeyExS
-- compromised PQ KEM secret keys set
  op pqkLeaked : Sys -> PqPriKeyS
-- compromised session keys set
  op hskLeaked : Sys -> KeyS
-- compromised long-term private keys set
  op ltkLeaked : Sys -> PriKeyTimeS
-- time of the system
  op time : Sys -> Nat 
```

`init` is defined in term of those obervers as follows:
```
  eq nw(init) = void .
  eq ur(init) = empty .
  eq uclk(init) = empty .
  eq upqk(init) = empty .
  eq ui(init) = empty .
  eq ss(init,A,B,I) = none .
  eq clkLeaked(init) = empty .
  eq pqkLeaked(init) = empty .
  eq hskLeaked(init) = empty .
  eq ltkLeaked(init) = pkNPair(priKey(intruder), 0) .
  eq time(init) = s(0) .
```

Moreover, we define `cpms`, `cclk`, `cpqk`, and `chsk` for the collection of pre-master secrets, ECDH shared keys, PQ KEM shared keys, and handshake keys, respectively, learned by the intruder.
```
-- pre-master secrets collection learned by the intruder
  op cpms : Sys -> ColPms
-- ECDH shared keys collection learned by the intruder
  op cclk : Sys -> ColClKey
-- PQ KEM shared keys collection learned by the intruder
  op cpqk : Sys -> ColPqKey
-- handshake keys collection learned by the intruder
  op chsk : Sys -> ColHsK

  eq PMS \in cpms(S) 
    = (pmsClKey(PMS) \in cclk(S) and pmsPqKey(PMS) \in cpqk(S)) .
  eq HSK \in chsk(S) = 
    (HSK \in hskLeaked(S) or 
     getPms(getMs(HSK)) \in cpms(S)) .
  eq KC \in cclk(S) = 
    ($clKey1(KC) \in clkLeaked(S) or 
     $clKey2(KC) \in clkLeaked(S) or 
     existClPriKexM(KC, nw(S))) .
  eq KP \in cpqk(S) = 
    ($pqKey1(KP) \in pqkLeaked(S) or 
     $pqKey2(KP) \in pqkLeaked(S) or 
     existPqPriKexM(KP, nw(S))) .
```

Now, we define the transitions declared above in term of equations:
`chello` is defined as follows:
```
  op c-chello : Sys Prin Rand -> Bool
  eq c-chello(S,A,R) = not(R \in ur(S)) .
  ceq nw(chello(S,A,B,V,R,CSs,KEMs)) = 
    (chM(A,A,B,V,R,CSs,KEMs) , nw(S)) if c-chello(S,A,R) .
  ceq ur(chello(S,A,B,V,R,CSs,KEMs)) = 
    (R ur(S)) if c-chello(S,A,R) .
  eq uclk(chello(S,A,B,V,R,CSs,KEMs)) = uclk(S) .
  eq upqk(chello(S,A,B,V,R,CSs,KEMs)) = upqk(S) .
  eq ui(chello(S,A,B,V,R,CSs,KEMs)) = ui(S) .
  eq ss(chello(S,A,B,V,R,CSs,KEMs),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(chello(S,A,B,V,R,CSs,KEMs)) = clkLeaked(S) .
  eq pqkLeaked(chello(S,A,B,V,R,CSs,KEMs)) = pqkLeaked(S) .
  eq hskLeaked(chello(S,A,B,V,R,CSs,KEMs)) = hskLeaked(S) .
  eq ltkLeaked(chello(S,A,B,V,R,CSs,KEMs)) = ltkLeaked(S) .
  eq time(chello(S,A,B,V,R,CSs,KEMs)) = time(S) .
  ceq chello(S,A,B,V,R,CSs,KEMs) = S if not c-chello(S,A,R) .
```

A transition is defined in term of equations specifying how observers change by the transition.
With `chello`, only observers `nw` and `ur` are changed by the transition.
We first define the effective condition `c-chello`, which states that the random `R` is not used before.
The transition says that if `R` is not used before, client `A` uses it to construct a `ClientHello` message and send it to server `B`, which is denoted by the message `chM(A,A,B,V,R,CSs,KEMs)` is put into the network in the successor state. Together with that, `R` is put into the set of used randoms.
For the other observers, there is no change.
The last equation states that if the effective condition is not satisfied, namely `R` is used before, then the state does not change.

In a similar way, we can define the following transition:
```
  op c-shello : Sys Rand CipherSuite Sid
    Prin Prin Prin Version Rand CipherSuites PqKemParams -> Bool
  eq c-shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs) = 
    (not(R2 \in ur(S) or I \in ui(S)) and   
     chM(A2,A,B,V,R,CSs,KEMs) \in nw(S) and
     CS \in CSs) .
  ceq nw(shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs)) = 
    (shM(B,B,A,V,R2,CS,I) , nw(S)) 
    if c-shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs) .
  ceq ur(shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs)) = 
    (R2 ur(S)) 
    if c-shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs) .
  eq uclk(shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs)) = uclk(S) .
  eq upqk(shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs)) = upqk(S) .
  ceq ui(shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs)) = 
    (I ui(S)) 
    if c-shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs) .
  eq ss(shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs),A9,B9,I9) = 
    ss(S,A9,B9,I9) .
  eq clkLeaked(shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs)) = clkLeaked(S) .
  eq pqkLeaked(shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs)) = pqkLeaked(S) .
  eq hskLeaked(shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs)) = hskLeaked(S) .
  eq ltkLeaked(shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs)) = ltkLeaked(S) .
  eq time(shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs)) = time(S) .
  ceq shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs) = S 
    if not c-shello(S,R2,CS,I,A2,A,B,V,R,CSs,KEMs) .
```

The equations say that if principal `B` has received a `ClientHello` message seemingly sent from `A`, random `R2` & session ID `I` have not been used before, and cipher suite `CS` is in the cipher suites list sent in the `ClientHello` message, then `B` replies to `A` with a `ServerHello` message using `R2`, `CS`, and `I`. Together with that, `R2` and `I` are put into the set of used random numbers and session IDs, respectively. If one of the conditions above is not satisfied, nothing changes. 
Note that the actual creator of the `ClientHello` message is `A2`, which may or may not equal `A`.

Similarly, we define transition `scert` specifying a server sends its certificate:

```
  op c-scert : Sys 
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid -> Bool
  eq c-scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I) = 
    (chM(A2,A,B,V,R,CSs,KEMs) \in nw(S) and
     shM(B,B,A,V,R2,CS,I) \in nw(S)) .
  ceq nw(scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = 
    (scertM(B,B,A,cert(B,pubKey(B),sign(ca,B,pubKey(B)))) , nw(S)) 
    if c-scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I) .
  eq ur(scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = ur(S) . 
  eq uclk(scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = uclk(S) .
  eq upqk(scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = upqk(S) .
  eq ui(scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = ui(S) . 
  eq ss(scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I),A9,B9,I9) = 
    ss(S,A9,B9,I9) .
  eq clkLeaked(scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = clkLeaked(S) . 
  eq pqkLeaked(scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = pqkLeaked(S) . 
  eq hskLeaked(scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = hskLeaked(S) . 
  eq ltkLeaked(scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = ltkLeaked(S) . 
  eq time(scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = time(S) . 
  ceq scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I) = S 
    if not c-scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I) .
```

The effective condition now is a server got a `ClientHello` message seemingly sent from `A` and the server has sent a `ServerHello` message back to the client.


Next, we define transition `skeyex` specifying a server sends a `ServerKeyExchange` message:

```
  op c-skeyex : Sys ClPriKeyEx PqPriKey
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid -> Bool
  op c-skeyex' : Sys
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid -> Bool
  eq c-skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I) = 
    (c-skeyex'(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I) and
     not (K \in uclk(S) or K' \in upqk(S)) ) .
  eq c-skeyex'(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I) = 
    (c-scert(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I) and
     scertM(B,B,A,cert(B,pubKey(B),sign(ca,B,pubKey(B)))) \in nw(S)) .

  ceq nw(skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = 
    (skexM(B,B,A,clPubKeyEx(K),pqPubKeyEn(K'),
      encH(priKey(B),hParams(R,R2,clPubKeyEx(K),pqPubKeyEn(K'))), time(S)) , 
     nw(S)) 
    if c-skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I) .
  eq ur(skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = ur(S) . 
  ceq uclk(skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I)) 
    = (K uclk(S))
    if c-skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I) .
  ceq upqk(skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I)) 
    = (K' upqk(S))
    if c-skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I) .
  eq ui(skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = ui(S) . 
  eq ss(skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I),A9,B9,I9) = 
    ss(S,A9,B9,I9) .
  eq clkLeaked(skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = clkLeaked(S) . 
  eq pqkLeaked(skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = pqkLeaked(S) . 
  eq hskLeaked(skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = hskLeaked(S) . 
  eq ltkLeaked(skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = ltkLeaked(S) . 
  ceq time(skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I)) = s(time(S))
    if c-skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I) .
  ceq skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I) = S 
    if not c-skeyex(S,K,K',A2,A,B,V,R,CSs,KEMs,R2,CS,I) .
```

The server uses two secret keys (ECDH and PQ KEM) `K` and `K'` to derive two correspond public keys `clPubKeyEx(K)` and `pqPubKeyEn(K')` to send them to the client.
In that message, time of the system, i.e., `time(S)`, is embedded at the end, and the time of the system is increment in the successor state, i.e., `s(time(S))`, where `s(N)` is `N + 1` (the successor of `N`).

A server sends a `CertificateRequest` message is specified by the following transition:
```
  op c-certReq : Sys 
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid 
    ClPriKeyEx PqPriKey Nat -> Bool
  eq c-certReq(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N) = 
    (c-skeyex'(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I) and
     skexM(B,B,A,clPubKeyEx(K),pqPubKeyEn(K'),
      encH(priKey(B),hParams(R,R2,clPubKeyEx(K),pqPubKeyEn(K'))),N) \in nw(S)) .
  ceq nw(certReq(S,CRTs,SGAs,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N)) 
    = (certReqM(B,B,A,CRTs,SGAs) , nw(S)) 
  if c-certReq(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N) .
  eq ur(certReq(S,CRTs,SGAs,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N)) = ur(S) .
  eq uclk(certReq(S,CRTs,SGAs,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N)) = uclk(S) .
  eq upqk(certReq(S,CRTs,SGAs,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N)) = upqk(S) .
  eq ui(certReq(S,CRTs,SGAs,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N)) = ui(S) .
  eq ss(certReq(S,CRTs,SGAs,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N),A9,B9,I9) 
    = ss(S,A9,B9,I9) .
  eq clkLeaked(certReq(S,CRTs,SGAs,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N)) 
    = clkLeaked(S) .
  eq pqkLeaked(certReq(S,CRTs,SGAs,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N)) 
    = pqkLeaked(S) .
  eq hskLeaked(certReq(S,CRTs,SGAs,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N))
    = hskLeaked(S) .
  eq ltkLeaked(certReq(S,CRTs,SGAs,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N))
    = ltkLeaked(S) .
  eq time(certReq(S,CRTs,SGAs,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N))
    = time(S) .
  ceq certReq(S,CRTs,SGAs,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N) = S
  if not c-certReq(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N) .
```

A server sends a `ServerHelloDone` message is specified as follows:
```
  op c-shelloDone : Sys 
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid 
    ClPriKeyEx PqPriKey Nat -> Bool
  eq c-shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N) = 
    (c-skeyex'(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I) and
     skexM(B,B,A,clPubKeyEx(K),pqPubKeyEn(K'),
      encH(priKey(B),hParams(R,R2,clPubKeyEx(K),pqPubKeyEn(K'))), N) 
     \in nw(S)) .
  ceq nw(shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N)) 
    = (shDnM(B,B,A) , nw(S)) 
  if c-shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N) .
  eq ur(shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N)) = ur(S) .
  eq uclk(shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N)) = uclk(S) .
  eq upqk(shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N)) = upqk(S) .
  eq ui(shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N)) = ui(S) .
  eq ss(shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N),A9,B9,I9) 
    = ss(S,A9,B9,I9) .
  eq clkLeaked(shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N)) 
    = clkLeaked(S) .
  eq pqkLeaked(shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N)) 
    = pqkLeaked(S) .
  eq hskLeaked(shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N))
    = hskLeaked(S) .
  eq ltkLeaked(shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N))
    = ltkLeaked(S) .
  eq time(shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N))
    = time(S) .
  ceq shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N) = S
  if not c-shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N) .
```

Upon receiving those messages from the server, the client first sends a `Certificate` message to the server as follows:

```
  op c-ccert : Sys
    Prin Prin Version Rand CipherSuites PqKemParams
    Prin Rand CipherSuite Sid 
    Cert
    ClPubKeyEx PqPubKey Cipher Nat
    CertTypes SignAlgs -> Bool
  eq c-ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs) 
    = (chM(A,A,B,V,R,CSs,KEMs) \in nw(S) and
     shM(B2,B,A,V,R2,CS,I) \in nw(S) and
     scertM(B2,B,A,CERT) \in nw(S) and
      sign(CERT) = sign(ca,owner(CERT),pubKey(CERT)) and
     skexM(B2,B,A,PK,PK',CI,N) \in nw(S) and
      decAsym?(CI,pubKey(CERT)) and
      decH(CI,pubKey(CERT)) = hParams(R,R2,PK,PK') and
     certReqM(B2,B,A,CRTs,SGAs) \in nw(S) and
     shDnM(B2,B,A) \in nw(S)) .
  ceq nw(ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs))
    = (ccertM(A,A,B,cert(A,pubKey(A),sign(ca,A,pubKey(A)))) , nw(S))
    if c-ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs) .
  eq ur(ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs)) = ur(S) . 
  eq uclk(ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs)) = uclk(S) .
  eq upqk(ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs)) = upqk(S) .
  eq ui(ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs)) = ui(S) . 
  eq ss(ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs),A9,B9,I9) 
    = ss(S,A9,B9,I9) .
  eq clkLeaked(ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs)) = clkLeaked(S) .
  eq pqkLeaked(ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs)) = pqkLeaked(S) .
  eq hskLeaked(ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs)) = hskLeaked(S) . 
  eq ltkLeaked(ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs)) = ltkLeaked(S) . 
  eq time(ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs)) = time(S) . 
  ceq ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs) = S 
    if not c-ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs) .
```

The effective condition states that client `A` must received valid `ServerHello`, `Certificate`, `ServerKeyExchange`, and `CertificateRequest` messages.

A client sends a `ClientKeyExchange` message is specified as follows:
```
  op c-ckeyex : Sys ClPriKeyEx PqPriKey
    Prin Prin Version Rand CipherSuites PqKemParams
    Prin Rand CipherSuite Sid 
    Cert
    ClPubKeyEx PqPubKey Cipher Nat 
    CertTypes SignAlgs -> Bool
  op c-ckeyex' : Sys
    Prin Prin Version Rand CipherSuites PqKemParams
    Prin Rand CipherSuite Sid 
    Cert
    ClPubKeyEx PqPubKey Cipher Nat 
    CertTypes SignAlgs -> Bool
  eq c-ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs) 
    = (c-ckeyex'(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
        CERT,PK,PK',CI,N,CRTs,SGAs) 
       and not (K2 \in uclk(S) or K2' \in upqk(S))) .
  eq c-ckeyex'(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs) 
    = (c-ccert(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
        CERT,PK,PK',CI,N,CRTs,SGAs) and
      ccertM(A,A,B,cert(A,pubKey(A),sign(ca,A,pubKey(A)))) \in nw(S)) .

  ceq nw(ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs))
    = (ckexM(A,A,B,clPubKeyEx(K2),encapsCipher(PK',K2'), time(S)) , nw(S)) 
    if c-ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs) .
  eq ur(ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs)) = ur(S) . 
  ceq uclk(ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs)) 
    = (K2 uclk(S))
    if c-ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs) .
  ceq upqk(ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs)) 
    = (K2' upqk(S))
    if c-ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs) .
  eq ui(ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs)) = ui(S) . 
  eq ss(ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs),A9,B9,I9) 
    = ss(S,A9,B9,I9) .
  eq clkLeaked(ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs)) = clkLeaked(S) .
  eq pqkLeaked(ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs)) = pqkLeaked(S) .
  eq hskLeaked(ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs)) = hskLeaked(S) . 
  eq ltkLeaked(ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs)) = ltkLeaked(S) . 
  ceq time(ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs)) = s(time(S))
    if c-ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs) .
  ceq ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs) = S 
    if not c-ckeyex(S,K2,K2',A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs) .
```

The effective condition states that client `A` must received valid `ServerHello`, `Certificate`, and `ServerKeyExchange` messages.
The definition of the transition can be understood likewise `skeyex`.

After that, the following transition specifies the client sends a `CertificateVerify` message, which is a signature of all handshake messages exchanged so far signed by the long-term private key of the client.

```
-- certificate verify
  op c-certVerify : Sys
    Prin Prin Version Rand CipherSuites PqKemParams
    Prin Rand CipherSuite Sid 
    Cert
    ClPubKeyEx PqPubKey Cipher Nat
    CertTypes SignAlgs
    ClPriKeyEx PqPriKey Nat -> Bool
  eq c-certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)
    = (c-ckeyex'(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
         CERT,PK,PK',CI,N,CRTs,SGAs) and
       ckexM(A,A,B,clPubKeyEx(K2),encapsCipher(PK',K2'),N2) \in nw(S) and
       N2 > N) .
  ceq nw(certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = 
    (certVerM(A,A,B,encH(priKey(A),
      hFullHs(A,B,V,R,CSs,KEMs,R2,CS,I,CERT,PK,PK',CI,
            CRTs,SGAs,cert(A,pubKey(A),sign(ca,A,pubKey(A))),
            clPubKeyEx(K2),encapsCipher(PK',K2')))) , nw(S)) 
    if c-certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2) .
  eq ur(certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = ur(S) . 
  eq uclk(certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = uclk(S) .
  eq upqk(certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = upqk(S) .
  eq ui(certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = ui(S) . 
  eq ss(certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = clkLeaked(S) . 
  eq pqkLeaked(certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = pqkLeaked(S) . 
  eq hskLeaked(certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = hskLeaked(S) . 
  eq ltkLeaked(certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = ltkLeaked(S) . 
  eq time(certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = time(S) . 
  ceq certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2) = S 
    if not c-certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2) .
```

A client sends a `ChangeCipherSpec` message is specified as follows:
```
  op c-cChangeCS : Sys
    Prin Prin Version Rand CipherSuites PqKemParams
    Prin Rand CipherSuite Sid 
    Cert
    ClPubKeyEx PqPubKey Cipher Nat 
    CertTypes SignAlgs
    ClPriKeyEx PqPriKey Nat -> Bool
  eq c-cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)
    = (c-certVerify(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
         CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2) and
       certVerM(A,A,B,encH(priKey(A),
        hFullHs(A,B,V,R,CSs,KEMs,R2,CS,I,CERT,PK,PK',CI,
            CRTs,SGAs,cert(A,pubKey(A),sign(ca,A,pubKey(A))),
            clPubKeyEx(K2),encapsCipher(PK',K2')))) \in nw(S)) .
  ceq nw(cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = 
    (ccsM(A,A,B) , nw(S)) 
    if c-cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2) .
  eq ur(cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = ur(S) . 
  eq uclk(cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = uclk(S) .
  eq upqk(cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = upqk(S) .
  eq ui(cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = ui(S) . 
  eq ss(cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = clkLeaked(S) . 
  eq pqkLeaked(cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = pqkLeaked(S) . 
  eq hskLeaked(cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = hskLeaked(S) . 
  eq ltkLeaked(cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = ltkLeaked(S) . 
  eq time(cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = time(S) . 
  ceq cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2) = S 
    if not c-cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2) .
```

After that, a client sends a `Finished` message by the following transition:

```
  op c-cfinish : Sys
    Prin Prin Version Rand CipherSuites PqKemParams
    Prin Rand CipherSuite Sid 
    Cert
    ClPubKeyEx PqPubKey Cipher Nat 
    CertTypes SignAlgs
    ClPriKeyEx PqPriKey Nat -> Bool
  eq c-cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)
    = (c-cChangeCS(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
        CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2) and
       ccsM(A,A,B) \in nw(S)) .
  ceq nw(cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = 
    (cfM(A,A,B, encFin(
        prf-ckey(prf-ms(classicKey(PK,K2) || pqKey(encapsKey(PK',K2'),N2), 
            seedMs(R,R2,clPubKeyEx(K2),encapsCipher(PK',K2'))), 
            seedHs(R,R2)),
        prf-cfin(prf-ms(classicKey(PK,K2) || pqKey(encapsKey(PK',K2'),N2), 
            seedMs(R,R2,clPubKeyEx(K2),encapsCipher(PK',K2'))), 
          hFullHs(A,B,V,R,CSs,KEMs,R2,CS,I,CERT,PK,PK',CI,
            CRTs,SGAs,cert(A,pubKey(A),sign(ca,A,pubKey(A))),
            clPubKeyEx(K2),encapsCipher(PK',K2')))
      )) , nw(S)) 
    if c-cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2) .
  eq ur(cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = ur(S) . 
  eq uclk(cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = uclk(S) .
  eq upqk(cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = upqk(S) .
  eq ui(cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = ui(S) . 
  eq ss(cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = clkLeaked(S) . 
  eq pqkLeaked(cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = pqkLeaked(S) . 
  eq hskLeaked(cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = hskLeaked(S) . 
  eq ltkLeaked(cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = ltkLeaked(S) . 
  eq time(cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
    CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2)) = time(S) . 
  ceq cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2) = S 
    if not c-cfinish(S,A,B,V,R,CSs,KEMs,B2,R2,CS,I,
      CERT,PK,PK',CI,N,CRTs,SGAs,K2,K2',N2) .
```

`PK` and `PK'` are ECDH and PQ KEM public keys that the client received from the server, while `K2` and `K2'` are the two secret keys used by the client. 
Note that the master secret is computed from the pre-master secret by the PRF function with the seed is tuple of the two randoms used in the two `Hello` messages, 
the ECDH public key and the PQ KEM ciphertext sent by the client in the `ClientKeyExchange` message.
While the handshake key is computed from the master secret with the seed is tuple of the two randoms used in the two `Hello` messages.
Note that handshake key used by the client is different from the handshake key used by the server (by using different label value in the PRF function).


A server sends a `ChangeCipherSpec` message is specified as follows:
```
  op c-sChangeCS : Sys
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid 
    ClPriKeyEx PqPriKey Nat
    CertTypes SignAlgs
    Prin Cert
    ClPubKeyEx PqCipher Nat
    Cipher -> Bool
  eq c-sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
      A3,CERT,PK2,EN,N2,CI) = 
    (c-shelloDone(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N) and
     shDnM(B,B,A) \in nw(S) and
     ccertM(A3,A,B,CERT) \in nw(S) and
      sign(CERT) = sign(ca,owner(CERT),pubKey(CERT)) and
     ckexM(A3,A,B,PK2,EN,N2) \in nw(S) and
     certVerM(A3,A,B,CI) \in nw(S) and
      decAsym?(CI, pubKey(CERT)) and 
      decH(CI,pubKey(CERT)) =
        hFullHs(A,B,V,R,CSs,KEMs,R2,CS,I,cert(B,pubKey(B),sign(ca,B,pubKey(B))),
          clPubKeyEx(K),pqPubKeyEn(K'),
          encH(priKey(B),hParams(R,R2,clPubKeyEx(K),pqPubKeyEn(K'))),
          CRTs,SGAs,CERT, PK2,EN) and
     cfM(A3,A,B,encFin(
        prf-ckey(prf-ms(classicKey(PK2,K) || pqKey(decaps(EN,K'),N2), 
          seedMs(R,R2,PK2,EN)), seedHs(R,R2)),
        prf-cfin(prf-ms(classicKey(PK2,K) || pqKey(decaps(EN,K'),N2), 
          seedMs(R,R2,PK2,EN)),
          hFullHs(A,B,V,R,CSs,KEMs,R2,CS,I, cert(B,pubKey(B),sign(ca,B,pubKey(B))),
            clPubKeyEx(K),pqPubKeyEn(K'),
            encH(priKey(B),hParams(R,R2,clPubKeyEx(K),pqPubKeyEn(K'))),
            CRTs,SGAs,CERT,PK2,EN)))) 
      \in nw(S) and
     ccsM(A3,A,B) \in nw(S)) .
  ceq nw(sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
      A3,CERT,PK2,EN,N2,CI)) 
    = (ccsM(B,B,A) , nw(S))
    if c-sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
      A3,CERT,PK2,EN,N2,CI) .
  eq ur(sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = ur(S) . 
  eq uclk(sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = uclk(S) .
  eq upqk(sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = upqk(S) .
  eq ui(sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = ui(S) . 
  eq ss(sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
      A3,CERT,PK2,EN,N2,CI),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = clkLeaked(S) . 
  eq pqkLeaked(sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = pqkLeaked(S) . 
  eq hskLeaked(sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = hskLeaked(S) . 
  eq ltkLeaked(sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = ltkLeaked(S) . 
  eq time(sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = time(S) . 
  ceq sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
      A3,CERT,PK2,EN,N2,CI) = S 
    if not c-sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
      A3,CERT,PK2,EN,N2,CI) .
```

After that, a server sends a `Finished` message by the following transition:
```
  op c-sfinish : Sys
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid 
    ClPriKeyEx PqPriKey Nat
    CertTypes SignAlgs
    Prin Cert
    ClPubKeyEx PqCipher Nat
    Cipher -> Bool
  eq c-sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
      A3,CERT,PK2,EN,N2,CI) = 
    (c-sChangeCS(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
      A3,CERT,PK2,EN,N2,CI) and
     ccsM(B,B,A) \in nw(S)) .
  ceq nw(sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
      A3,CERT,PK2,EN,N2,CI)) 
    = (sfM(B,B,A, encFin(
        prf-skey(prf-ms(classicKey(PK2,K) || pqKey(decaps(EN,K'),N2),
            seedMs(R,R2,PK2,EN)), seedHs(R,R2)),
        prf-sfin(prf-ms(classicKey(PK2,K) || pqKey(decaps(EN,K'),N2), 
            seedMs(R,R2,PK2,EN)),
          hFullHs(A,B,V,R,CSs,KEMs, R2,CS,I, cert(B,pubKey(B),sign(ca,B,pubKey(B))),
            clPubKeyEx(K),pqPubKeyEn(K'),
            encH(priKey(B),hParams(R,R2,clPubKeyEx(K),pqPubKeyEn(K'))),
            CRTs,SGAs,CERT,PK2,EN))
      )) , nw(S)) 
    if c-sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
      A3,CERT,PK2,EN,N2,CI) .
  eq ur(sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = ur(S) . 
  eq uclk(sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = uclk(S) .
  eq upqk(sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = upqk(S) .
  eq ui(sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = ui(S) . 
  ceq ss(sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
      A3,CERT,PK2,EN,N2,CI),A9,B9,I9) = 
    (if A9 = A and B9 = B and I9 = I 
     then session(I,CS,prf-ms(classicKey(PK2,K) || pqKey(decaps(EN,K'),N2), 
          seedMs(R,R2,PK2,EN)))
     else ss(S,A9,B9,I9) 
     fi) 
    if c-sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
      A3,CERT,PK2,EN,N2,CI) .
  eq clkLeaked(sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = clkLeaked(S) . 
  eq pqkLeaked(sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = pqkLeaked(S) . 
  eq hskLeaked(sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = hskLeaked(S) . 
  eq ltkLeaked(sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = ltkLeaked(S) . 
  eq time(sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
    A3,CERT,PK2,EN,N2,CI)) = time(S) . 
  ceq sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
      A3,CERT,PK2,EN,N2,CI) = S 
    if not c-sfinish(S,A2,A,B,V,R,CSs,KEMs,R2,CS,I,K,K',N,CRTs,SGAs,
      A3,CERT,PK2,EN,N2,CI) .
```

For the effective condition, the server must validate the `Finished` message received from the client.
At this step, session between the client and the server is established, which stores the session ID, the selected cipher suite, and the master secret.

We complete specify the full handshake mode, now we change to specify the abrreviated handshake mode. 
Firstly, a client sends `ClientHello` message as follows:

```
  op c-chello2 : Sys Prin Prin Version Rand Sid CipherSuites -> Bool
  eq c-chello2(S,A,B,V,R,I,CSs) = 
    (not(R \in ur(S)) and not(ss(S,A,B,I) = none) and
     cs(ss(S,A,B,I)) \in CSs) .
  ceq nw(chello2(S,A,B,V,R,I,CSs)) =
      (ch2M(A,A,B,V,R,I,CSs) , nw(S)) 
    if c-chello2(S,A,B,V,R,I,CSs) .
  ceq ur(chello2(S,A,B,V,R,I,CSs)) = 
    (R ur(S)) if c-chello2(S,A,B,V,R,I,CSs) .
  eq uclk(chello2(S,A,B,V,R,I,CSs)) = uclk(S) .
  eq upqk(chello2(S,A,B,V,R,I,CSs)) = upqk(S) .
  eq ui(chello2(S,A,B,V,R,I,CSs)) = ui(S) .
  eq ss(chello2(S,A,B,V,R,I,CSs),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(chello2(S,A,B,V,R,I,CSs)) = clkLeaked(S) .
  eq pqkLeaked(chello2(S,A,B,V,R,I,CSs)) = pqkLeaked(S) .
  eq hskLeaked(chello2(S,A,B,V,R,I,CSs)) = hskLeaked(S) .
  eq ltkLeaked(chello2(S,A,B,V,R,I,CSs)) = ltkLeaked(S) .
  eq time(chello2(S,A,B,V,R,I,CSs)) = time(S) .
  ceq chello2(S,A,B,V,R,I,CSs) = S 
    if not c-chello2(S,A,B,V,R,I,CSs) .
```

The effective condition states that if there exists a previously established session between client `A` and server `B`, denoted by `not(ss(S,A,B,I) = none)`, then `A` can use the session ID and the selected cipher suite in that session to construct a `ClientHello` message and send it to `B`.

Upon receiving the `ClientHello` message, `B` replies back to `A` as follows:

```
  op c-shello2 : Sys Rand
    Prin Prin Prin Version Rand Sid CipherSuites -> Bool
  eq c-shello2(S,R2,A2,A,B,V,R,I,CSs) = 
    (ch2M(A2,A,B,V,R,I,CSs) \in nw(S) and
     not(R2 \in ur(S)) and not(ss(S,A,B,I) = none) and
     cs(ss(S,A,B,I)) \in CSs) .
  ceq nw(shello2(S,R2,A2,A,B,V,R,I,CSs)) =
      (sh2M(B,B,A,V,R2,I,cs(ss(S,A,B,I))) , nw(S)) 
    if c-shello2(S,R2,A2,A,B,V,R,I,CSs) .
  ceq ur(shello2(S,R2,A2,A,B,V,R,I,CSs)) = 
    (R2 ur(S)) if c-shello2(S,R2,A2,A,B,V,R,I,CSs) .
  eq uclk(shello2(S,R2,A2,A,B,V,R,I,CSs)) = uclk(S) .
  eq upqk(shello2(S,R2,A2,A,B,V,R,I,CSs)) = upqk(S) .
  eq ui(shello2(S,R2,A2,A,B,V,R,I,CSs)) = ui(S) .
  eq ss(shello2(S,R2,A2,A,B,V,R,I,CSs),A9,B9,I9) 
    = ss(S,A9,B9,I9) .
  eq clkLeaked(shello2(S,R2,A2,A,B,V,R,I,CSs)) = clkLeaked(S) .
  eq pqkLeaked(shello2(S,R2,A2,A,B,V,R,I,CSs)) = pqkLeaked(S) .
  eq hskLeaked(shello2(S,R2,A2,A,B,V,R,I,CSs)) = hskLeaked(S) .
  eq ltkLeaked(shello2(S,R2,A2,A,B,V,R,I,CSs)) = ltkLeaked(S) .
  eq time(shello2(S,R2,A2,A,B,V,R,I,CSs)) = time(S) .
  ceq shello2(S,R2,A2,A,B,V,R,I,CSs) = S 
    if not c-shello2(S,R2,A2,A,B,V,R,I,CSs) .

  op c-sChangeCS2 : Sys
    Prin Prin Prin Version Rand Sid CipherSuites 
    Rand -> Bool
  eq c-sChangeCS2(S,A2,A,B,V,R,I,CSs,R2) = 
    (not(ss(S,A,B,I) = none) and
      ch2M(A2,A,B,V,R,I,CSs) \in nw(S) and
     sh2M(B,B,A,V,R2,I,cs(ss(S,A,B,I))) \in nw(S)) .
  ceq nw(sChangeCS2(S,A2,A,B,V,R,I,CSs,R2)) =
      (ccsM(B,B,A) , nw(S))
    if c-sChangeCS2(S,A2,A,B,V,R,I,CSs,R2) .
  eq ur(sChangeCS2(S,A2,A,B,V,R,I,CSs,R2)) = ur(S) .
  eq uclk(sChangeCS2(S,A2,A,B,V,R,I,CSs,R2)) = uclk(S) .
  eq upqk(sChangeCS2(S,A2,A,B,V,R,I,CSs,R2)) = upqk(S) .
  eq ui(sChangeCS2(S,A2,A,B,V,R,I,CSs,R2)) = ui(S) .
  eq ss(sChangeCS2(S,A2,A,B,V,R,I,CSs,R2),A9,B9,I9) 
    = ss(S,A9,B9,I9) .
  eq clkLeaked(sChangeCS2(S,A2,A,B,V,R,I,CSs,R2)) = clkLeaked(S) .
  eq pqkLeaked(sChangeCS2(S,A2,A,B,V,R,I,CSs,R2)) = pqkLeaked(S) .
  eq hskLeaked(sChangeCS2(S,A2,A,B,V,R,I,CSs,R2)) = hskLeaked(S) .
  eq ltkLeaked(sChangeCS2(S,A2,A,B,V,R,I,CSs,R2)) = ltkLeaked(S) .
  eq time(sChangeCS2(S,A2,A,B,V,R,I,CSs,R2)) = time(S) .
  ceq sChangeCS2(S,A2,A,B,V,R,I,CSs,R2) = S 
    if not c-sChangeCS2(S,A2,A,B,V,R,I,CSs,R2) .
```

`B` first sends a `ServerHello` back, and then sends a `ChangeCipherSpec` message.
After that, `B` jumps to send a `Finished` message.

```
  op c-sfinish2 : Sys
    Prin Prin Prin Version Rand Sid CipherSuites 
    Rand -> Bool
  eq c-sfinish2(S,A2,A,B,V,R,I,CSs,R2) = 
    c-sChangeCS2(S,A2,A,B,V,R,I,CSs,R2) and
    ccsM(B,B,A) \in nw(S) .
  ceq nw(sfinish2(S,A2,A,B,V,R,I,CSs,R2)) =
      (sf2M(B,B,A,encFin(
          prf-skey(ms(ss(S,A,B,I)), seedHs(R,R2)),
          prf-sfin2(ms(ss(S,A,B,I)),
            hAbbrHs(A,B,V,R,I,CSs,R2,cs(ss(S,A,B,I))))
        )) , nw(S)) 
    if c-sfinish2(S,A2,A,B,V,R,I,CSs,R2) .
  eq ur(sfinish2(S,A2,A,B,V,R,I,CSs,R2)) = ur(S) .
  eq uclk(sfinish2(S,A2,A,B,V,R,I,CSs,R2)) = uclk(S) .
  eq upqk(sfinish2(S,A2,A,B,V,R,I,CSs,R2)) = upqk(S) .
  eq ui(sfinish2(S,A2,A,B,V,R,I,CSs,R2)) = ui(S) .
  eq ss(sfinish2(S,A2,A,B,V,R,I,CSs,R2),A9,B9,I9) 
    = ss(S,A9,B9,I9) .
  eq clkLeaked(sfinish2(S,A2,A,B,V,R,I,CSs,R2)) = clkLeaked(S) .
  eq pqkLeaked(sfinish2(S,A2,A,B,V,R,I,CSs,R2)) = pqkLeaked(S) .
  eq hskLeaked(sfinish2(S,A2,A,B,V,R,I,CSs,R2)) = hskLeaked(S) .
  eq ltkLeaked(sfinish2(S,A2,A,B,V,R,I,CSs,R2)) = ltkLeaked(S) .
  eq time(sfinish2(S,A2,A,B,V,R,I,CSs,R2)) = time(S) .
  ceq sfinish2(S,A2,A,B,V,R,I,CSs,R2) = S 
    if not c-sfinish2(S,A2,A,B,V,R,I,CSs,R2) .
```

Client `A` does the same thing, sending a `ChangeCipherSpec` message followed by a `Finished` message.
```
  op c-cChangeCS2 : Sys
    Prin Prin Version Rand Sid CipherSuites 
    Prin Rand 
    Prin
    Prin -> Bool
  eq c-cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4) = 
    (not(ss(S,A,B,I) = none) and
     ch2M(A,A,B,V,R,I,CSs) \in nw(S) and
     sh2M(B2,B,A,V,R2,I,cs(ss(S,A,B,I))) \in nw(S) and
     ccsM(B3,B,A) \in nw(S) and
     sf2M(B4,B,A,encFin(
        prf-skey(ms(ss(S,A,B,I)), seedHs(R,R2)),
        prf-sfin2(ms(ss(S,A,B,I)),
          hAbbrHs(A,B,V,R,I,CSs,R2,cs(ss(S,A,B,I))))))
      \in nw(S)) .
  ceq nw(cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) =
      (ccsM(A,A,B), nw(S)) 
    if c-cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4) .
  eq ur(cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = ur(S) .
  eq uclk(cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = uclk(S) .
  eq upqk(cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = upqk(S) .
  eq ui(cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = ui(S) .
  eq ss(cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4),A9,B9,I9) 
    = ss(S,A9,B9,I9) .
  eq clkLeaked(cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = clkLeaked(S) .
  eq pqkLeaked(cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = pqkLeaked(S) .
  eq hskLeaked(cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = hskLeaked(S) .
  eq ltkLeaked(cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = ltkLeaked(S) .
  eq time(cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = time(S) .
  ceq cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4) = S 
    if not c-cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4) .

  op c-cfinish2 : Sys
    Prin Prin Version Rand Sid CipherSuites 
    Prin Rand 
    Prin
    Prin -> Bool
  eq c-cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4) = 
    c-cChangeCS2(S,A,B,V,R,I,CSs,B2,R2,B3,B4) and
    ccsM(A,A,B) \in nw(S) .
  ceq nw(cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) =
      (cf2M(A,A,B,encFin(
          prf-ckey(ms(ss(S,A,B,I)), seedHs(R,R2)),
          prf-cfin2(ms(ss(S,A,B,I)),
            hAbbrHs(A,B,V,R,I,CSs,R2,cs(ss(S,A,B,I))))
        )) , nw(S)) 
    if c-cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4) .
  eq ur(cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = ur(S) .
  eq uclk(cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = uclk(S) .
  eq upqk(cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = upqk(S) .
  eq ui(cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = ui(S) .
  eq ss(cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4),A9,B9,I9) 
    = ss(S,A9,B9,I9) .
  eq clkLeaked(cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = clkLeaked(S) .
  eq pqkLeaked(cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = pqkLeaked(S) .
  eq hskLeaked(cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = hskLeaked(S) .
  eq ltkLeaked(cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = ltkLeaked(S) .
  eq time(cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4)) = time(S) .
  ceq cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4) = S 
    if not c-cfinish2(S,A,B,V,R,I,CSs,B2,R2,B3,B4) .
```

A server can send a `HelloRequest` message at any time to request the client sends a `ClientHello` message:
```
  eq nw(helloReq(S,A,B)) = (heReM(B,B,A) , nw(S)) .
  eq ur(helloReq(S,A,B)) = ur(S) .
  eq uclk(helloReq(S,A,B)) = uclk(S) .
  eq upqk(helloReq(S,A,B)) = upqk(S) .
  eq ui(helloReq(S,A,B)) = ui(S) .
  eq ss(helloReq(S,A,B),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(helloReq(S,A,B)) = clkLeaked(S) .
  eq pqkLeaked(helloReq(S,A,B)) = pqkLeaked(S) .
  eq hskLeaked(helloReq(S,A,B)) = hskLeaked(S) .
  eq ltkLeaked(helloReq(S,A,B)) = ltkLeaked(S) .
  eq time(helloReq(S,A,B)) = time(S) .
```

We now specify the intruder capabilities.
Firstly, the intruder can impersonate `A` to send a `ClientHello` message to `B` as follows:
```
  eq nw(fkChello(S,A,B,V,R,CSs,KEMs)) = 
    (chM(intruder,A,B,V,R,CSs,KEMs) , nw(S)) .
  eq ur(fkChello(S,A,B,V,R,CSs,KEMs)) = ur(S) .
  eq uclk(fkChello(S,A,B,V,R,CSs,KEMs)) = uclk(S) .
  eq upqk(fkChello(S,A,B,V,R,CSs,KEMs)) = upqk(S) .
  eq ui(fkChello(S,A,B,V,R,CSs,KEMs)) = ui(S) .
  eq ss(fkChello(S,A,B,V,R,CSs,KEMs),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkChello(S,A,B,V,R,CSs,KEMs)) = clkLeaked(S) .
  eq pqkLeaked(fkChello(S,A,B,V,R,CSs,KEMs)) = pqkLeaked(S) .
  eq hskLeaked(fkChello(S,A,B,V,R,CSs,KEMs)) = hskLeaked(S) .
  eq ltkLeaked(fkChello(S,A,B,V,R,CSs,KEMs)) = ltkLeaked(S) .
  eq time(fkChello(S,A,B,V,R,CSs,KEMs)) = time(S) .
```

where `A` and `B` denote arbitrary principals;
`V`, `R`, `CSs`, and `KEMs` can be arbitrary protocol version, random number, cipher suites list, and PQ KEM parameters.
The `ClientHello` message, as we can see now the first argument is `intruder` but not `A`. Recall that the first, second, and third arguments respectively denote the actual creator, the seeming sender, and the receiver of that message.
So with `chM(intruder,A,B,V,R,CSs,KEMs)`, the intruder is impersonating `A` to send that message to `B`.

Similarly, the intruder can fake a `ServerHello` message:
```
  eq nw(fkShello(S,B,A,V,R,CS,I)) = 
    (shM(intruder,B,A,V,R,CS,I) , nw(S)) .
  eq ur(fkShello(S,B,A,V,R,CS,I)) = ur(S) .
  eq uclk(fkShello(S,B,A,V,R,CS,I)) = uclk(S) .
  eq upqk(fkShello(S,B,A,V,R,CS,I)) = upqk(S) .
  eq ui(fkShello(S,B,A,V,R,CS,I)) = ui(S) .
  eq ss(fkShello(S,B,A,V,R,CS,I),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkShello(S,B,A,V,R,CS,I)) = clkLeaked(S) .
  eq pqkLeaked(fkShello(S,B,A,V,R,CS,I)) = pqkLeaked(S) .
  eq hskLeaked(fkShello(S,B,A,V,R,CS,I)) = hskLeaked(S) .
  eq ltkLeaked(fkShello(S,B,A,V,R,CS,I)) = ltkLeaked(S) .
  eq time(fkShello(S,B,A,V,R,CS,I)) = time(S) .
```

The intruder can fake a `Certificate` message, which is specified by the following transition:
```
  op c-fkCert : Sys Prin Prin PubKey Sign -> Bool
  eq c-fkCert(S,B,A,PKE,G) = G \in csign(nw(S)) .
  ceq nw(fkCert(S,B,A,PKE,G)) 
      = (scertM(intruder,B,A,cert(B,PKE,G)) , nw(S))
    if c-fkCert(S,B,A,PKE,G) .
  eq ur(fkCert(S,B,A,PKE,G)) = ur(S) .
  eq uclk(fkCert(S,B,A,PKE,G)) = uclk(S) .
  eq upqk(fkCert(S,B,A,PKE,G)) = upqk(S) .
  eq ui(fkCert(S,B,A,PKE,G)) = ui(S) .
  eq ss(fkCert(S,B,A,PKE,G),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkCert(S,B,A,PKE,G)) = clkLeaked(S) .
  eq pqkLeaked(fkCert(S,B,A,PKE,G)) = pqkLeaked(S) .
  eq hskLeaked(fkCert(S,B,A,PKE,G)) = hskLeaked(S) .
  eq ltkLeaked(fkCert(S,B,A,PKE,G)) = ltkLeaked(S) .
  eq time(fkCert(S,B,A,PKE,G)) = time(S) .
  ceq fkCert(S,B,A,PKE,G) = S 
    if not c-fkCert(S,B,A,PKE,G) .
```

The effective condition states that a signature `G` must be learned by the intruder.
Based on such a `G`, the intruder can fake a certificate, and use it to construct a `Certificate` message and send the message to some other.

The following transition specifies the intruder fakes a `ServerKeyExchange` message:
```
  op c-fkSkeyex : Sys Prin ClPriKeyEx PqPriKey -> Bool
  eq c-fkSkeyex(S,B,K,K') 
    = not (K \in uclk(S) or K' \in upqk(S))
      and priKey(B) \in' ltkLeaked(S) .
  ceq nw(fkSkeyex(S,B,A,K,K',R,R2)) = 
    (skexM(intruder,B,A,clPubKeyEx(K),pqPubKeyEn(K'),
      encH(priKey(B), hParams(R,R2,clPubKeyEx(K),pqPubKeyEn(K'))), time(S)) , 
     nw(S)) 
  if c-fkSkeyex(S,B,K,K') .
  eq ur(fkSkeyex(S,B,A,K,K',R,R2)) = ur(S) .
  ceq uclk(fkSkeyex(S,B,A,K,K',R,R2)) = (K uclk(S))
  if c-fkSkeyex(S,B,K,K') .
  ceq upqk(fkSkeyex(S,B,A,K,K',R,R2)) = (K' upqk(S))
  if c-fkSkeyex(S,B,K,K') .
  eq ui(fkSkeyex(S,B,A,K,K',R,R2)) = ui(S) .
  eq ss(fkSkeyex(S,B,A,K,K',R,R2),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkSkeyex(S,B,A,K,K',R,R2)) = clkLeaked(S) .
  eq pqkLeaked(fkSkeyex(S,B,A,K,K',R,R2)) = pqkLeaked(S) .
  eq hskLeaked(fkSkeyex(S,B,A,K,K',R,R2)) = hskLeaked(S) .
  eq ltkLeaked(fkSkeyex(S,B,A,K,K',R,R2)) = ltkLeaked(S) .
  ceq time(fkSkeyex(S,B,A,K,K',R,R2)) = s(time(S)) 
  if c-fkSkeyex(S,B,K,K') .
  ceq fkSkeyex(S,B,A,K,K',R,R2) = S 
  if not c-fkSkeyex(S,B,K,K') .
```

The equations say that if the long-term private key of `B` has been compromised and two secret keys `K` and `K'` have not been used before (can be arbitrary),
then the intruder constructs a `ServerKeyExchange` message from the two secret keys, sign them with the compromised key, and impersonate `B` to send the message to `A`.
Together with that, the current time is embedded at the end of the message and the time of the system is incremented. 

Moreover, we also define another transition on faking a `ServerKeyExchange` message:

```
  op c-fkSkeyex2 : Sys Prin Prin ClPriKeyEx PqPriKey Rand Rand -> Bool
  eq c-fkSkeyex2(S,B,A,K,K',R,R2) 
    = (K \in clkLeaked(S) and K' \in pqkLeaked(S)) .
  ceq nw(fkSkeyex2(S,B,A,K,K',R,R2)) = 
    (skexM(intruder,B,A,clPubKeyEx(K),pqPubKeyEn(K'),
      encH(priKey(intruder), hParams(R,R2,clPubKeyEx(K),pqPubKeyEn(K'))), time(S)) , nw(S)) 
  if c-fkSkeyex2(S,B,A,K,K',R,R2) .
  eq ur(fkSkeyex2(S,B,A,K,K',R,R2)) = ur(S) .
  eq uclk(fkSkeyex2(S,B,A,K,K',R,R2)) = uclk(S) .
  eq upqk(fkSkeyex2(S,B,A,K,K',R,R2)) = upqk(S) .
  eq ui(fkSkeyex2(S,B,A,K,K',R,R2)) = ui(S) .
  eq ss(fkSkeyex2(S,B,A,K,K',R,R2),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkSkeyex2(S,B,A,K,K',R,R2)) = clkLeaked(S) .
  eq pqkLeaked(fkSkeyex2(S,B,A,K,K',R,R2)) = pqkLeaked(S) .
  eq hskLeaked(fkSkeyex2(S,B,A,K,K',R,R2)) = hskLeaked(S) .
  eq ltkLeaked(fkSkeyex2(S,B,A,K,K',R,R2)) = ltkLeaked(S) .
  ceq time(fkSkeyex2(S,B,A,K,K',R,R2)) = s(time(S)) 
  if c-fkSkeyex2(S,B,A,K,K',R,R2) .
  ceq fkSkeyex2(S,B,A,K,K',R,R2) = S 
    if not c-fkSkeyex2(S,B,A,K,K',R,R2) .
```

The effective condition states that the two secret keys `K` and `K'` are compromised.
Besides,
`fkSkeyex2` is different from `fkSkeyex` in the signature over the two public keys.
Here, the intruder does not know the long-term private of `B`, so the intruder can only use his/her private key to sign the two public keys.

Similarly, we define two transitions on faking a `ClientKeyExchange` message:
```
  op c-fkCkeyex : Sys ClPriKeyEx PqPriKey -> Bool
  eq c-fkCkeyex(S,K,K') = not (K \in uclk(S) or K' \in upqk(S)) .
  ceq nw(fkCkeyex(S,A,B,K,K',PK')) = 
    (ckexM(intruder,A,B,clPubKeyEx(K),encapsCipher(PK',K'), time(S)) , nw(S)) 
  if c-fkCkeyex(S,K,K') .
  eq ur(fkCkeyex(S,A,B,K,K',PK')) = ur(S) .
  ceq uclk(fkCkeyex(S,A,B,K,K',PK')) = (K uclk(S))
  if c-fkCkeyex(S,K,K') .
  ceq upqk(fkCkeyex(S,A,B,K,K',PK')) = (K' upqk(S))
  if c-fkCkeyex(S,K,K') .
  eq ui(fkCkeyex(S,A,B,K,K',PK')) = ui(S) .
  eq ss(fkCkeyex(S,A,B,K,K',PK'),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkCkeyex(S,A,B,K,K',PK')) = clkLeaked(S) .
  eq pqkLeaked(fkCkeyex(S,A,B,K,K',PK')) = pqkLeaked(S) .
  eq hskLeaked(fkCkeyex(S,A,B,K,K',PK')) = hskLeaked(S) .
  eq ltkLeaked(fkCkeyex(S,A,B,K,K',PK')) = ltkLeaked(S) .
  ceq time(fkCkeyex(S,A,B,K,K',PK')) = s(time(S))
  if c-fkCkeyex(S,K,K') .
  ceq fkCkeyex(S,A,B,K,K',PK') = S 
    if not c-fkCkeyex(S,K,K') .

  op c-fkCkeyex2 : Sys Prin Prin ClPriKeyEx PqPriKey -> Bool
  eq c-fkCkeyex2(S,A,B,K,K') 
    = (K \in clkLeaked(S) and K' \in pqkLeaked(S)) .
  ceq nw(fkCkeyex2(S,A,B,K,K',PK')) = 
    (ckexM(intruder,A,B,clPubKeyEx(K),encapsCipher(PK',K'), time(S)) , nw(S)) 
  if c-fkCkeyex2(S,A,B,K,K') .
  eq ur(fkCkeyex2(S,A,B,K,K',PK')) = ur(S) .
  eq uclk(fkCkeyex2(S,A,B,K,K',PK')) = uclk(S) .
  eq upqk(fkCkeyex2(S,A,B,K,K',PK')) = upqk(S) .
  eq ui(fkCkeyex2(S,A,B,K,K',PK')) = ui(S) .
  eq ss(fkCkeyex2(S,A,B,K,K',PK'),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkCkeyex2(S,A,B,K,K',PK')) = clkLeaked(S) .
  eq pqkLeaked(fkCkeyex2(S,A,B,K,K',PK')) = pqkLeaked(S) .
  eq hskLeaked(fkCkeyex2(S,A,B,K,K',PK')) = hskLeaked(S) .
  eq ltkLeaked(fkCkeyex2(S,A,B,K,K',PK')) = ltkLeaked(S) .
  ceq time(fkCkeyex2(S,A,B,K,K',PK')) = s(time(S))
  if c-fkCkeyex2(S,A,B,K,K') .
  ceq fkCkeyex2(S,A,B,K,K',PK') = S
    if not c-fkCkeyex2(S,A,B,K,K') .
```

The following transition specifies how intruder can impersonate client `A` to send a `Finished` message to server `B`:

```
  op c-fkCfinish : Sys Pms Sign Sign -> Bool
  eq c-fkCfinish(S,PMS,G,G2) 
    = (PMS \in cpms(S) and 
       G \in csign(nw(S)) and G2 \in csign(nw(S))) .
  ceq nw(fkCfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
      R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) 
    = (cfM(intruder,A,B,encFin(
        prf-ckey(prf-ms(PMS, seedMs(R,R2,PK2,EN)), seedHs(R,R2)),
        prf-cfin(prf-ms(PMS, seedMs(R,R2,PK2,EN)),
          hFullHs(A,B,V,R,CSs,KEMs, R2,CS,I, cert(B,PKE,G),
            PK,PK',CI,CRTs,SGAs,cert(A,PKE2,G2),PK2,EN))
        )) , nw(S)) 
    if c-fkCfinish(S,PMS,G,G2) .
  eq ur(fkCfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = ur(S) .
  eq uclk(fkCfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = uclk(S) .
  eq upqk(fkCfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = upqk(S) .
  eq ui(fkCfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = ui(S) .
  eq ss(fkCfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs), A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkCfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = clkLeaked(S) .
  eq pqkLeaked(fkCfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = pqkLeaked(S) .
  eq hskLeaked(fkCfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = hskLeaked(S) .
  eq ltkLeaked(fkCfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = ltkLeaked(S) .
  eq time(fkCfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = time(S) .
  ceq fkCfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
      R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs) = S 
    if not c-fkCfinish(S,PMS,G,G2) .
```

The effective condition states that the intruder must have learned pre-master secret `PMS` and two signatures `G` and `G2`.
In that case, the intruder can use the pre-master secret to derive the master secret and the handshake key on the client side, and then construct a `Finished` message to send to some other.
Here, `PKE`, `V`, `R`, `CSs`, `KEMs`, `R2`, `CS`, `I`, `PK`, `PK'`, `CI`, `PK2`, and `EN` can receive arbitrary values of their sorts.
Those values can be grasped from some messages in the network since they are all sent in plaintext.
For example, `CI` can be grasped from the `ServerKeyExchange` message created and sent by `B` to `A`, which is the valid ciphertext obtained by encrypting two public keys sent in that message and the two random numbers sent in the same session under the long-term private key of `B`.

Similarly, we can specify how the intruder can impersonate a server to send a `Finished` message:

```
  op c-fkSfinish : Sys Pms Sign Sign -> Bool
  eq c-fkSfinish(S,PMS,G,G2) = c-fkCfinish(S,PMS,G,G2) .
  ceq nw(fkSfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) 
    = (sfM(intruder,B,A,encFin(
        prf-skey(prf-ms(PMS, seedMs(R,R2,PK2,EN)), seedHs(R,R2)),
        prf-sfin(prf-ms(PMS, seedMs(R,R2,PK2,EN)),
          hFullHs(A,B,V,R,CSs,KEMs, R2,CS,I, cert(B,PKE,G),
            PK,PK',CI,CRTs,SGAs,cert(A,PKE2,G2),PK2,EN))
        )) , nw(S)) 
    if c-fkSfinish(S,PMS,G,G2) .
  eq ur(fkSfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = ur(S) .
  eq uclk(fkSfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = uclk(S) .
  eq upqk(fkSfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = upqk(S) .
  eq ui(fkSfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = ui(S) .
  eq ss(fkSfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs), A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkSfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = clkLeaked(S) .
  eq pqkLeaked(fkSfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = pqkLeaked(S) .
  eq hskLeaked(fkSfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = hskLeaked(S) .
  eq ltkLeaked(fkSfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = ltkLeaked(S) .
  eq time(fkSfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = time(S) .
  ceq fkSfinish(S,PMS,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
      R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs) = S 
    if not c-fkSfinish(S,PMS,G,G2) .
```

Faking `ServerHelloDone`, `ChangeCipherSpec`, are specified by the following two transitions:

```
  eq nw(fkShelloDone(S,B,A)) = 
    (shDnM(intruder,B,A) , nw(S)) .
  eq ur(fkShelloDone(S,B,A)) = ur(S) .
  eq uclk(fkShelloDone(S,B,A)) = uclk(S) .
  eq upqk(fkShelloDone(S,B,A)) = upqk(S) .
  eq ui(fkShelloDone(S,B,A)) = ui(S) .
  eq ss(fkShelloDone(S,B,A),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkShelloDone(S,B,A)) = clkLeaked(S) .
  eq pqkLeaked(fkShelloDone(S,B,A)) = pqkLeaked(S) .
  eq hskLeaked(fkShelloDone(S,B,A)) = hskLeaked(S) .
  eq ltkLeaked(fkShelloDone(S,B,A)) = ltkLeaked(S) .
  eq time(fkShelloDone(S,B,A)) = time(S) .

  eq nw(fkChangeCS(S,A,B)) = 
    (ccsM(intruder,A,B) , nw(S)) .
  eq ur(fkChangeCS(S,A,B)) = ur(S) .
  eq uclk(fkChangeCS(S,A,B)) = uclk(S) .
  eq upqk(fkChangeCS(S,A,B)) = upqk(S) .
  eq ui(fkChangeCS(S,A,B)) = ui(S) .
  eq ss(fkChangeCS(S,A,B),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkChangeCS(S,A,B)) = clkLeaked(S) .
  eq pqkLeaked(fkChangeCS(S,A,B)) = pqkLeaked(S) .
  eq hskLeaked(fkChangeCS(S,A,B)) = hskLeaked(S) .
  eq ltkLeaked(fkChangeCS(S,A,B)) = ltkLeaked(S) .
  eq time(fkChangeCS(S,A,B)) = time(S) .
```

In this case, when client authentication is requested, three more transitions are defined, specifying the intruder fakes `CertificateRequest`, client `Certificate` and `CertificateVerify` messages.
The first and second ones are modeled by the following two transitions:

```
  eq nw(fkCertReq(S,B,A,CRTs,SGAs)) = 
    (certReqM(intruder,B,A,CRTs,SGAs) , nw(S)) .
  eq ur(fkCertReq(S,B,A,CRTs,SGAs)) = ur(S) .
  eq uclk(fkCertReq(S,B,A,CRTs,SGAs)) = uclk(S) .
  eq upqk(fkCertReq(S,B,A,CRTs,SGAs)) = upqk(S) .
  eq ui(fkCertReq(S,B,A,CRTs,SGAs)) = ui(S) .
  eq ss(fkCertReq(S,B,A,CRTs,SGAs),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkCertReq(S,B,A,CRTs,SGAs)) = clkLeaked(S) .
  eq pqkLeaked(fkCertReq(S,B,A,CRTs,SGAs)) = pqkLeaked(S) .
  eq hskLeaked(fkCertReq(S,B,A,CRTs,SGAs)) = hskLeaked(S) .
  eq ltkLeaked(fkCertReq(S,B,A,CRTs,SGAs)) = ltkLeaked(S) .
  eq time(fkCertReq(S,B,A,CRTs,SGAs)) = time(S) .

  op c-fkCCert : Sys Prin Prin PubKey Sign -> Bool
  eq c-fkCCert(S,B,A,PKE,G) = G \in csign(nw(S)) .
  ceq nw(fkCCert(S,B,A,PKE,G)) 
      = (ccertM(intruder,B,A,cert(B,PKE,G)) , nw(S))
    if c-fkCCert(S,B,A,PKE,G) .
  eq ur(fkCCert(S,B,A,PKE,G)) = ur(S) .
  eq uclk(fkCCert(S,B,A,PKE,G)) = uclk(S) .
  eq upqk(fkCCert(S,B,A,PKE,G)) = upqk(S) .
  eq ui(fkCCert(S,B,A,PKE,G)) = ui(S) .
  eq ss(fkCCert(S,B,A,PKE,G),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkCCert(S,B,A,PKE,G)) = clkLeaked(S) .
  eq pqkLeaked(fkCCert(S,B,A,PKE,G)) = pqkLeaked(S) .
  eq hskLeaked(fkCCert(S,B,A,PKE,G)) = hskLeaked(S) .
  eq ltkLeaked(fkCCert(S,B,A,PKE,G)) = ltkLeaked(S) .
  eq time(fkCCert(S,B,A,PKE,G)) = time(S) .
  ceq fkCCert(S,B,A,PKE,G) = S 
    if not c-fkCCert(S,B,A,PKE,G) .
```

The third one is specified as follows:

```
  op c-fkCertVerify : Sys Sign Sign -> Bool
  eq c-fkCertVerify(S,G,G2) 
    = (G \in csign(nw(S)) and G2 \in csign(nw(S))) .
  ceq nw(fkCertVerify(S,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
      R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) 
    = (certVerM(intruder,A,B,encH(priKey(intruder),
        hFullHs(A,B,V,R,CSs,KEMs,R2,CS,I,cert(B,PKE,G),
          PK,PK',CI,CRTs,SGAs,cert(A,PKE2,G2),PK2,EN))) , nw(S)) 
    if c-fkCertVerify(S,G,G2) .
  eq ur(fkCertVerify(S,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = ur(S) .
  eq uclk(fkCertVerify(S,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = uclk(S) .
  eq upqk(fkCertVerify(S,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = upqk(S) .
  eq ui(fkCertVerify(S,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = ui(S) .
  eq ss(fkCertVerify(S,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs), A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkCertVerify(S,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = clkLeaked(S) .
  eq pqkLeaked(fkCertVerify(S,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = pqkLeaked(S) .
  eq hskLeaked(fkCertVerify(S,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = hskLeaked(S) .
  eq ltkLeaked(fkCertVerify(S,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = ltkLeaked(S) .
  ceq time(fkCertVerify(S,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
    R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs)) = s(time(S))
    if c-fkCertVerify(S,G,G2) .
  ceq fkCertVerify(S,PKE,G,PKE2,G2,A,B,V,R,CSs,KEMs,
      R2,CS,I,PK,PK',CI,PK2,EN,CRTs,SGAs) = S 
    if not c-fkCertVerify(S,G,G2) .
```

The effective condition states that the intruder must have learned two signatures `G` and `G2`, from which the intruder can build a `CertificateVerify` message.

For the abbreviated handshake mode, we can specify the intruder capabilities in a similar way.
First, let us define two transitions specifying the intruder fakes `ClientHello` and `ServerHello` messages in the abbreviated handshake mode:

```
  eq nw(fkChello2(S,A,B,V,R,I,CSs)) = 
    (ch2M(intruder,A,B,V,R,I,CSs) , nw(S)) .
  eq ur(fkChello2(S,A,B,V,R,I,CSs)) = ur(S) .
  eq uclk(fkChello2(S,A,B,V,R,I,CSs)) = uclk(S) .
  eq upqk(fkChello2(S,A,B,V,R,I,CSs)) = upqk(S) .
  eq ui(fkChello2(S,A,B,V,R,I,CSs)) = ui(S) .
  eq ss(fkChello2(S,A,B,V,R,I,CSs),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkChello2(S,A,B,V,R,I,CSs)) = clkLeaked(S) .
  eq pqkLeaked(fkChello2(S,A,B,V,R,I,CSs)) = pqkLeaked(S) .
  eq hskLeaked(fkChello2(S,A,B,V,R,I,CSs)) = hskLeaked(S) .
  eq ltkLeaked(fkChello2(S,A,B,V,R,I,CSs)) = ltkLeaked(S) .
  eq time(fkChello2(S,A,B,V,R,I,CSs)) = time(S) .

  eq nw(fkShello2(S,B,A,V,R,I,CS)) = 
    (sh2M(intruder,B,A,V,R,I,CS) , nw(S)) .
  eq ur(fkShello2(S,B,A,V,R,I,CS)) = ur(S) .
  eq uclk(fkShello2(S,B,A,V,R,I,CS)) = uclk(S) .
  eq upqk(fkShello2(S,B,A,V,R,I,CS)) = upqk(S) .
  eq ui(fkShello2(S,B,A,V,R,I,CS)) = ui(S) .
  eq ss(fkShello2(S,B,A,V,R,I,CS),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(fkShello2(S,B,A,V,R,I,CS)) = clkLeaked(S) .
  eq pqkLeaked(fkShello2(S,B,A,V,R,I,CS)) = pqkLeaked(S) .
  eq hskLeaked(fkShello2(S,B,A,V,R,I,CS)) = hskLeaked(S) .
  eq ltkLeaked(fkShello2(S,B,A,V,R,I,CS)) = ltkLeaked(S) .
  eq time(fkShello2(S,B,A,V,R,I,CS)) = time(S) .
```

Faking `Finished` messages in the abbreviated handshake mode is specified as follows:

```
  op c-fkCfinish2 : Sys Pms -> Bool
  eq c-fkCfinish2(S,PMS) = PMS \in cpms(S) .
  ceq nw(fkCfinish2(S,A,B,V,R,I,CSs,R2,PMS,CS,PK2,EN)) =
      (cf2M(intruder,A,B,encFin(
          prf-ckey(prf-ms(PMS, seedMs(R,R2,PK2,EN)), seedHs(R,R2)),
          prf-cfin2(prf-ms(PMS, seedMs(R,R2,PK2,EN)),
            hAbbrHs(A,B,V,R,I,CSs,R2,CS))
        )) , nw(S)) 
    if c-fkCfinish2(S,PMS) .
  eq ur(fkCfinish2(S,A,B,V,R,I,CSs,R2,PMS,CS,PK2,EN)) = ur(S) .
  eq uclk(fkCfinish2(S,A,B,V,R,I,CSs,R2,PMS,CS,PK2,EN)) = uclk(S) .
  eq upqk(fkCfinish2(S,A,B,V,R,I,CSs,R2,PMS,CS,PK2,EN)) = upqk(S) .
  eq ui(fkCfinish2(S,A,B,V,R,I,CSs,R2,PMS,CS,PK2,EN)) = ui(S) .
  eq ss(fkCfinish2(S,A,B,V,R,I,CSs,R2,PMS,CS,PK2,EN),A9,B9,I9) 
    = ss(S,A9,B9,I9) .
  eq clkLeaked(fkCfinish2(S,A,B,V,R,I,CSs,R2,PMS,CS,PK2,EN)) 
    = clkLeaked(S) .
  eq pqkLeaked(fkCfinish2(S,A,B,V,R,I,CSs,R2,PMS,CS,PK2,EN)) 
    = pqkLeaked(S) .
  eq hskLeaked(fkCfinish2(S,A,B,V,R,I,CSs,R2,PMS,CS,PK2,EN)) 
    = hskLeaked(S) .
  eq ltkLeaked(fkCfinish2(S,A,B,V,R,I,CSs,R2,PMS,CS,PK2,EN)) 
    = ltkLeaked(S) .
  eq time(fkCfinish2(S,A,B,V,R,I,CSs,R2,PMS,CS,PK2,EN)) 
    = time(S) .
  ceq fkCfinish2(S,A,B,V,R,I,CSs,R2,PMS,CS,PK2,EN) = S 
    if not c-fkCfinish2(S,PMS) .

  op c-fkSfinish2 : Sys Pms -> Bool
  eq c-fkSfinish2(S,PMS) = PMS \in cpms(S) .
  ceq nw(fkSfinish2(S,B,A,V,R,I,CSs,R2,PMS,CS,PK2,EN)) =
      (sf2M(intruder,B,A,encFin(
          prf-skey(prf-ms(PMS, seedMs(R,R2,PK2,EN)), seedHs(R,R2)),
          prf-sfin2(prf-ms(PMS, seedMs(R,R2,PK2,EN)),
            hAbbrHs(A,B,V,R,I,CSs,R2,CS))
        )) , nw(S)) 
    if c-fkSfinish2(S,PMS) .
  eq ur(fkSfinish2(S,B,A,V,R,I,CSs,R2,PMS,CS,PK2,EN)) = ur(S) .
  eq uclk(fkSfinish2(S,B,A,V,R,I,CSs,R2,PMS,CS,PK2,EN)) = uclk(S) .
  eq upqk(fkSfinish2(S,B,A,V,R,I,CSs,R2,PMS,CS,PK2,EN)) = upqk(S) .
  eq ui(fkSfinish2(S,B,A,V,R,I,CSs,R2,PMS,CS,PK2,EN)) = ui(S) .
  eq ss(fkSfinish2(S,B,A,V,R,I,CSs,R2,PMS,CS,PK2,EN),A9,B9,I9) 
    = ss(S,A9,B9,I9) .
  eq clkLeaked(fkSfinish2(S,B,A,V,R,I,CSs,R2,PMS,CS,PK2,EN)) 
    = clkLeaked(S) .
  eq pqkLeaked(fkSfinish2(S,B,A,V,R,I,CSs,R2,PMS,CS,PK2,EN)) 
    = pqkLeaked(S) .
  eq hskLeaked(fkSfinish2(S,B,A,V,R,I,CSs,R2,PMS,CS,PK2,EN)) 
    = hskLeaked(S) .
  eq ltkLeaked(fkSfinish2(S,B,A,V,R,I,CSs,R2,PMS,CS,PK2,EN)) 
    = ltkLeaked(S) .
  eq time(fkSfinish2(S,B,A,V,R,I,CSs,R2,PMS,CS,PK2,EN)) 
    = time(S) .
  ceq fkSfinish2(S,B,A,V,R,I,CSs,R2,PMS,CS,PK2,EN) = S 
    if not c-fkSfinish2(S,PMS) .
```

Our threat model allows the compromises of (1) symmetric handshake keys, (2) ECDHE secret keys, (3) PQ KEM secret keys, and (4) long-term private keys of honest principals. 
The definitions of two transitions modeling the compromise of ECDH secret keys are as follows:

```
  op c-leakPKE1 : Sys Prin Prin Prin ClPubKeyEx PqPubKey Cipher Nat -> Bool
  eq c-leakPKE1(S,A,A2,A3,PK,PK',CI,N) = 
    skexM(A,A2,A3,PK,PK',CI,N) \in nw(S) .
  eq nw(leakPKE1(S,A,A2,A3,PK,PK',CI,N)) = nw(S) .
  eq ur(leakPKE1(S,A,A2,A3,PK,PK',CI,N)) = ur(S) .
  eq uclk(leakPKE1(S,A,A2,A3,PK,PK',CI,N)) = uclk(S) .
  eq upqk(leakPKE1(S,A,A2,A3,PK,PK',CI,N)) = upqk(S) .
  eq ui(leakPKE1(S,A,A2,A3,PK,PK',CI,N)) = ui(S) .
  eq ss(leakPKE1(S,A,A2,A3,PK,PK',CI,N),A9,B9,I9) = ss(S,A9,B9,I9) .
  ceq clkLeaked(leakPKE1(S,A,A2,A3,PK,PK',CI,N)) 
      = (clkLeaked(S) priClKey(PK)) 
    if c-leakPKE1(S,A,A2,A3,PK,PK',CI,N) .
  eq pqkLeaked(leakPKE1(S,A,A2,A3,PK,PK',CI,N)) = pqkLeaked(S) .
  eq hskLeaked(leakPKE1(S,A,A2,A3,PK,PK',CI,N)) = hskLeaked(S) .
  eq ltkLeaked(leakPKE1(S,A,A2,A3,PK,PK',CI,N)) = ltkLeaked(S) .
  eq time(leakPKE1(S,A,A2,A3,PK,PK',CI,N)) = time(S) .
  ceq leakPKE1(S,A,A2,A3,PK,PK',CI,N) = S 
    if not c-leakPKE1(S,A,A2,A3,PK,PK',CI,N) .

  op c-leakPKE3 : Sys Prin Prin Prin ClPubKeyEx PqCipher Nat -> Bool
  eq c-leakPKE3(S,A,A2,A3,PK,EN,N) = 
    ckexM(A,A2,A3,PK,EN,N) \in nw(S) .
  eq nw(leakPKE3(S,A,A2,A3,PK,EN,N)) = nw(S) .
  eq ur(leakPKE3(S,A,A2,A3,PK,EN,N)) = ur(S) .
  eq uclk(leakPKE3(S,A,A2,A3,PK,EN,N)) = uclk(S) .
  eq upqk(leakPKE3(S,A,A2,A3,PK,EN,N)) = upqk(S) .
  eq ui(leakPKE3(S,A,A2,A3,PK,EN,N)) = ui(S) .
  eq ss(leakPKE3(S,A,A2,A3,PK,EN,N),A9,B9,I9) = ss(S,A9,B9,I9) .
  ceq clkLeaked(leakPKE3(S,A,A2,A3,PK,EN,N)) 
      = (clkLeaked(S) priClKey(PK)) 
    if c-leakPKE3(S,A,A2,A3,PK,EN,N) .
  eq pqkLeaked(leakPKE3(S,A,A2,A3,PK,EN,N)) = pqkLeaked(S) .
  eq hskLeaked(leakPKE3(S,A,A2,A3,PK,EN,N)) = hskLeaked(S) .
  eq ltkLeaked(leakPKE3(S,A,A2,A3,PK,EN,N)) = ltkLeaked(S) .
  eq time(leakPKE3(S,A,A2,A3,PK,EN,N)) = time(S) .
  ceq leakPKE3(S,A,A2,A3,PK,EN,N) = S 
    if not c-leakPKE3(S,A,A2,A3,PK,EN,N) .
```

The two transitions say that when there exists a `ServerKeyExchange` message or a `ClientKeyExchange` message in the network where the ECDH public key `PK` is sent,
then the associated secret key of `PK` is compromised and added to the set of compromised ECDH secret keys in the successor state.


Similarly, we define two transitions modeling the compromise of PQ KEM secret keys:

```
  op c-leakPKE2 : Sys Prin Prin Prin ClPubKeyEx PqPubKey Cipher Nat -> Bool
  eq c-leakPKE2(S,A,A2,A3,PK,PK',CI,N) = 
    c-leakPKE1(S,A,A2,A3,PK,PK',CI,N) .
  eq nw(leakPKE2(S,A,A2,A3,PK,PK',CI,N)) = nw(S) .
  eq ur(leakPKE2(S,A,A2,A3,PK,PK',CI,N)) = ur(S) .
  eq uclk(leakPKE2(S,A,A2,A3,PK,PK',CI,N)) = uclk(S) .
  eq upqk(leakPKE2(S,A,A2,A3,PK,PK',CI,N)) = upqk(S) .
  eq ui(leakPKE2(S,A,A2,A3,PK,PK',CI,N)) = ui(S) .
  eq ss(leakPKE2(S,A,A2,A3,PK,PK',CI,N),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(leakPKE2(S,A,A2,A3,PK,PK',CI,N)) = clkLeaked(S) .
  ceq pqkLeaked(leakPKE2(S,A,A2,A3,PK,PK',CI,N)) 
    = (pqkLeaked(S) priPqKey(PK')) 
    if c-leakPKE2(S,A,A2,A3,PK,PK',CI,N) .
  eq hskLeaked(leakPKE2(S,A,A2,A3,PK,PK',CI,N)) = hskLeaked(S) .
  eq ltkLeaked(leakPKE2(S,A,A2,A3,PK,PK',CI,N)) = ltkLeaked(S) .
  eq time(leakPKE2(S,A,A2,A3,PK,PK',CI,N)) = time(S) .
  ceq leakPKE2(S,A,A2,A3,PK,PK',CI,N) = S 
    if not c-leakPKE2(S,A,A2,A3,PK,PK',CI,N) .

  op c-leakPKE4 : Sys Prin Prin Prin ClPubKeyEx PqCipher Nat -> Bool
  eq c-leakPKE4(S,A,A2,A3,PK,EN,N) = 
    c-leakPKE3(S,A,A2,A3,PK,EN,N) .
  eq nw(leakPKE4(S,A,A2,A3,PK,EN,N)) = nw(S) .
  eq ur(leakPKE4(S,A,A2,A3,PK,EN,N)) = ur(S) .
  eq uclk(leakPKE4(S,A,A2,A3,PK,EN,N)) = uclk(S) .
  eq upqk(leakPKE4(S,A,A2,A3,PK,EN,N)) = upqk(S) .
  eq ui(leakPKE4(S,A,A2,A3,PK,EN,N)) = ui(S) .
  eq ss(leakPKE4(S,A,A2,A3,PK,EN,N),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(leakPKE4(S,A,A2,A3,PK,EN,N)) = clkLeaked(S) .
  ceq pqkLeaked(leakPKE4(S,A,A2,A3,PK,EN,N)) 
    = (pqkLeaked(S) priPqKey(EN)) 
    if c-leakPKE4(S,A,A2,A3,PK,EN,N) .
  eq hskLeaked(leakPKE4(S,A,A2,A3,PK,EN,N)) = hskLeaked(S) .
  eq ltkLeaked(leakPKE4(S,A,A2,A3,PK,EN,N)) = ltkLeaked(S) .
  eq time(leakPKE4(S,A,A2,A3,PK,EN,N)) = time(S) .
  ceq leakPKE4(S,A,A2,A3,PK,EN,N) = S 
    if not c-leakPKE4(S,A,A2,A3,PK,EN,N) .
```

Compromise of symmetric handshake keys are modeled as follows:

```
  op c-leakHsK : Sys Prin Prin Key FinVD -> Bool
  eq c-leakHsK(S,A,B,HSK,FVD) = 
    (cfM(A,A,B,encFin(HSK,FVD)) \in nw(S) or
     sfM(A,A,B,encFin(HSK,FVD)) \in nw(S))  .
  eq nw(leakHsK(S,A,B,HSK,FVD)) = nw(S) .
  eq ur(leakHsK(S,A,B,HSK,FVD)) = ur(S) .
  eq uclk(leakHsK(S,A,B,HSK,FVD)) = uclk(S) .
  eq upqk(leakHsK(S,A,B,HSK,FVD)) = upqk(S) .
  eq ui(leakHsK(S,A,B,HSK,FVD)) = ui(S) .
  eq ss(leakHsK(S,A,B,HSK,FVD),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(leakHsK(S,A,B,HSK,FVD)) = clkLeaked(S) .
  eq pqkLeaked(leakHsK(S,A,B,HSK,FVD)) = pqkLeaked(S) .
  ceq hskLeaked(leakHsK(S,A,B,HSK,FVD)) 
      = (hskLeaked(S) HSK)
    if c-leakHsK(S,A,B,HSK,FVD) .
  eq ltkLeaked(leakHsK(S,A,B,HSK,FVD)) = ltkLeaked(S) .
  eq time(leakHsK(S,A,B,HSK,FVD)) = time(S) .
  ceq leakHsK(S,A,B,HSK,FVD) = S 
    if not c-leakHsK(S,A,B,HSK,FVD) .
```

The equations say that when there exists a `Finished` message in the network where its ciphertext is encrypted by the handshake key `HSK`, then `HSK` is compromised and added to the set of compromised handshake keys.

Finally, the compromise of long-term private keys of some principals is modeled by the following transition:

```
  op c-leakLtK : Sys Prin -> Bool
  eq c-leakLtK(S,A) = not (priKey(A) \in' ltkLeaked(S)) .
  eq nw(leakLtK(S,A)) = nw(S) .
  eq ur(leakLtK(S,A)) = ur(S) .
  eq uclk(leakLtK(S,A)) = uclk(S) .
  eq upqk(leakLtK(S,A)) = upqk(S) .
  eq ui(leakLtK(S,A)) = ui(S) .
  eq ss(leakLtK(S,A),A9,B9,I9) = ss(S,A9,B9,I9) .
  eq clkLeaked(leakLtK(S,A)) = clkLeaked(S) .
  eq pqkLeaked(leakLtK(S,A)) = pqkLeaked(S) .
  eq hskLeaked(leakLtK(S,A)) = hskLeaked(S) .
  ceq ltkLeaked(leakLtK(S,A)) = (pkNPair(priKey(A), time(S)) ltkLeaked(S)) 
  if c-leakLtK(S,A) .
  ceq time(leakLtK(S,A)) = s(time(S)) 
  if c-leakLtK(S,A) .
  ceq leakLtK(S,A) = S 
    if not c-leakLtK(S,A) .
```

The equations straightforwardly say that a long-term private key of any principal can be compromised.
