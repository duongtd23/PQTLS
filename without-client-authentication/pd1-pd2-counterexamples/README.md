## Two invalid invariant candidates `pd1` and `pd2` and their counterexamples

### pd1:
`pd1` says that when honest client `A` has sent to honest server `B` a Finished message indicating that the key negotiation has been completed in which the two ECDH secret keys of the shared secret are not compromised, then the intruder cannot learn ECDH shared secret.

In the open-close fragment,
eight fresh constants `s1`,...,`s8` of the sort `Sys` denote eight states in which there is a sequence of transition instances: `init` -> `s1`, `s1` -> `s2`,..., `s7` -> `s8`. 
<!-- The definitions of chello, scert, skeyex, shelloDone, ckeyex, cChangeCS, and cfinish are shown and explained in the webpage mentioned in Chapter 1. -->

The three macros `pqCipher`, `signPrs`, and `certB` are used because there are several occurrences of the corresponding terms in the fragment. 
However, their employments are not mandatory. 
Running this open-close fragment, false will be returned, meaning that `pd1` does not hold in the state `s8`. 
From the initial state, client `a` starts sending a ClientHello message to server `b`, and the system state changes to `s1`. 
`b` replies back to `a` with four messages: ServerHello, Certificate, ServerKeyExchange, and ServerHelloDone, respectively changing the system state to `s2`, `s3`, `s4`, and `s5`. 
Then, `a` sends three messages: ClientKeyExchange, ChangeCipherSpec, and Finished, respectively changing the system state to `s6`, `s7`, and `s8`. 
Now, `pd1` is violated in the last state `s8`. 
It can be understood easily since the intruder can grasp the two ECDH public keys carried in the ServerKeyExchange and ClientKeyExchange messages, and then derives the shared secret. 

----
### pd2:
`pd2` is the counterpart of `ssKeySe`, i.e., session key secrecy property, but stated from a server's point of view.

Running the open-close fragment above, false will be returned. 
The transition sequence can be paraphrased as follows. 
Initially, the intruder impersonates client `a` to send a ClientHello message to server `b`. 
Upon receiving the message, `b`, on their belief thinks that the message is sent by `a`, replies back to `a` with four messages: ServerHello, Certificate, ServerKeyExchange, and ServerHelloDone. 
The intruder intercepts the four messages, then chooses two secret keys, i.e., `k2` and `k2'`, to construct a ClientKeyExchange message, and acts as `a` to sends the message to `b`. 
The intruder continuously fakes and sends to `b` a ChangeCipherSpec message. 
From `k2`, `k2'`, and the public keys grasped from the ServerKeyExchange message, the intruder computes the pre-master secrets, master secret, and the handshake keys to construct a Finished message, and sends it to `b`. 
Upon receiving the three messages (again, on the belief that they are sent by `a`), `b` validates them, computes the symmetric keys, and then sends back to `a` ChangeCipherSpec and Finished messages. 
Now, in this state, `pd2` is violated because the intruder already learned the symmetric keys. Precisely, the reason is that the intruder has completely impersonated `a` and intercepted messages sent from `b` to communicate with `b`.
