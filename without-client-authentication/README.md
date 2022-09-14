### Contents:
- `hbtls-wtca.cafe`: the specification of the protocol without client authentication.
- `invariants.cafe`: all invariants/lemmas.
- others: proof scores, for example, `gen2.cafe` is the generated proof score for `inv2`.
- `inputs`: folder contains all input files for IPSG tool.

----
### CafeOBJ specification: a detail description
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

Next, we model random numbers, cipher suites, session IDs, protocol versions, and PQ KEM parameters used in the `ClientHello` message (note that comments in CafeOBJ are started with `--` and finished at the end of that line):

```
mod! RANDOM {
  [Rand]
}
mod! CIPHER-SUITE {
  [CipherSuite]
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
mod! ENCRYPTION {
  pr(HANDSHAKE-KEY + CERTIFICATE + SID + PROTOCOL-VERSION)
  pr(LIST(D <= TRIV2CIPHER-SUITE)*{sort List -> CipherSuites})
  pr(LIST(D <= TRIV2PQ-KEM-PARAM)*{sort List -> PqKemParams})
  [Cipher] [Hash] [FinVD]

-- for verify_datas
  op prf-cfin  : Ms Hash -> FinVD {constr}
  op prf-sfin  : Ms Hash -> FinVD {constr}
  op prf-cfin2 : Ms Hash -> FinVD {constr}
  op prf-sfin2 : Ms Hash -> FinVD {constr}

-- for hash functions
  op hFullHs : Prin Prin Version Rand CipherSuites PqKemParams Rand 
    CipherSuite Sid Cert ClPubKeyEx PqPubKey Cipher ClPubKeyEx PqCipher 
    -> Hash {constr}
  op hAbbrHs : Prin Prin Version Rand Sid CipherSuites Rand CipherSuite 
    -> Hash {constr}
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
  vars CERT CERT2 : Cert 
  vars KEMs KEMs2 : PqKemParams
  vars FVD FVD' FVD2 : FinVD
  vars V V2 : Version
  vars EN EN2 : PqCipher

  eq (hFullHs(A,B,V,R,CSs,KEMs,R2,CS,I,CERT,PK,PK',CI,PK2,EN) =
      hFullHs(A2,B2,V2,R3,CSs2,KEMs2,R4,CS2,I2,CERT2,PK3,PK3',CI2,PK4,EN2)) =
    (A = A2 and B = B2 and R = R3 and CSs = CSs2 and 
     KEMs = KEMs2 and R2 = R4 and CS = CS2 and I = I2 and 
     CERT = CERT2 and PK = PK3 and PK' = PK3' and 
     CI = CI2 and PK2 = PK4 and EN = EN2 and V = V2) .   
  eq (hAbbrHs(A,B,V,R,I,CSs,R2,CS) =
      hAbbrHs(A2,B2,V2,R3,I2,CSs2,R4,CS2)) =
    (A = A2 and B = B2 and R = R3 and CSs = CSs2 and 
     R2 = R4 and CS = CS2 and I = I2 and V = V2) . 
  eq (hParams(R,R2,PK,PK') = hParams(R3,R4,PK2,PK2')) =
    (R = R3 and R2 = R4 and PK = PK2 and PK' = PK2') .
  eq (hFullHs(A,B,V,R,CSs,KEMs,R2,CS,I,CERT,PK,PK',CI,PK2,EN) =
      hAbbrHs(A2,B2,V2,R3,I2,CSs2,R4,CS2)) = false .
  eq (hFullHs(A,B,V,R,CSs,KEMs,R2,CS,I,CERT,PK,PK',CI,PK2,EN) =
      hParams(R3,R4,PK3,PK3')) = false .
  eq (hAbbrHs(A,B,V,R,I,CSs,R2,CS) = hParams(R3,R4,PK2,PK2')) = false .
  eq (encH(KE, H) = encH(KE2, H2)) = (KE = KE2 and H = H2) .
  eq (encFin(KR,FVD) = encFin(KR2,FVD2)) = (KR = KR2 and FVD = FVD2) .  
  eq (prf-cfin(MS,H) = prf-cfin(MS2,H2)) = (MS = MS2 and H = H2) .
  eq (prf-sfin(MS,H) = prf-sfin(MS2,H2)) = (MS = MS2 and H = H2) .
  eq (prf-cfin2(MS,H) = prf-cfin2(MS2,H2)) = (MS = MS2 and H = H2) .
  eq (prf-sfin2(MS,H) = prf-sfin2(MS2,H2)) = (MS = MS2 and H = H2) .
}
```
<!-- Note that -->

We then introduce module `MESSAGE` modeling messages exchanged in the protocol. The module first declares sort `Msg` with 14 constructors where their explanations are given in the code comments:
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
-- sending server hello done 
  op shelloDone : Sys 
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid 
    ClPriKeyEx PqPriKey Nat -> Sys {constr}
-- sending client key exchange 
  op ckeyex : Sys ClPriKeyEx PqPriKey
    Prin Prin Version Rand CipherSuites PqKemParams
    Prin Rand CipherSuite Sid 
    Cert
    ClPubKeyEx PqPubKey Cipher Nat -> Sys {constr}
-- sending client change cipher spec
  op cChangeCS : Sys
    Prin Prin Version Rand CipherSuites PqKemParams
    Prin Rand CipherSuite Sid 
    Cert
    ClPubKeyEx PqPubKey Cipher Nat 
    ClPriKeyEx PqPriKey Nat -> Sys {constr}
-- sending client finished
  op cfinish : Sys 
    Prin Prin Version Rand CipherSuites PqKemParams
    Prin Rand CipherSuite Sid
    Cert
    ClPubKeyEx PqPubKey Cipher Nat 
    ClPriKeyEx PqPriKey Nat -> Sys {constr}
-- sending server change cipher spec
  op sChangeCS : Sys
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid
    ClPriKeyEx PqPriKey Nat
    Prin ClPubKeyEx PqCipher Nat -> Sys {constr}
-- sending server finished
  op sfinish : Sys 
    Prin Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid
    ClPriKeyEx PqPriKey Nat
    Prin ClPubKeyEx PqCipher Nat -> Sys {constr}
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
  op fkCfinish : Sys Pms PubKey Sign
    Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid
    ClPubKeyEx PqPubKey Cipher
    ClPubKeyEx PqCipher -> Sys {constr}
-- faking server finished
  op fkSfinish : Sys Pms PubKey Sign
    Prin Prin Version Rand CipherSuites PqKemParams
    Rand CipherSuite Sid
    ClPubKeyEx PqPubKey Cipher
    ClPubKeyEx PqCipher -> Sys {constr}
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























