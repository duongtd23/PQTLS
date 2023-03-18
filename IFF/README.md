## Formal verification of the IFF protocol

This is an authentication protocol that verifies whether a principal is a member of a group. There are some different groups, where each group is given a unique symmetric key in advance and each principal belongs to only one group. Let A and B denote two principals. The protocol consists of two messages exchanged as follows:

    Check A -> B : r
    Reply B -> A : senc(k, r ; B)

senc denotes symmetric encryption and ; is the concatenation operator. Whenever A wants to determine whether B is also a part of A's group, A first selects a fresh random r and sends it to B via a Check message. Upon receiving that message, B replies to A with a Reply message whose content is the received random and the ID of B encrypted by the symmetric key of B's group, i.e., k. Upon receiving that Reply message, A will know that B also belongs to the same group if A successfully decrypts the ciphertext using their group’s symmetric key and the plaintext contains r and B.

We verify the *identifiable* property, whose informal description is as follows: if principal A receives a valid Reply message and A believes that the message was sent by B, B belongs to the same group with A. 
The property is specified as `inv1` in the specification (`iff.cafe`), and is proved by using an additional lemma, namely `inv2`.

- `iff.cafe`: the specification of IFF in CafeOBJ.
- `proof-scores.cafe`: the proof scores of `inv1` and `inv2`.
- `input.cafe`: the input commands for IPSG to generate the proof scores.