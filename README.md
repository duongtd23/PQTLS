## Security verification of Hybrid Post-Quantum TLS Handshake Protocol
In this repository, you can find:

1. `IFF`: IFF protocol specification in CafeOBJ and its proof scores to verify the  *identifiable property*.

2. `without-client-authentication`: The specification and verification of the Hybrid PQ TLS in case client authentication is **not** requested.
You can find the description of the contents of this folder and a detailed explanation of the formal specification in the README file in this folder.

3. `with-client-authentication`: The specification and verification of the Hybrid PQ TLS in case client authentication is requested.
Similarly, you can find the description of the contents of this folder and a detailed explanation of the formal specification in the README file in this folder.



## Tools installation
Our verification requires the use of CafeInMaude, which can be downloaded from here: https://github.com/ariesco/CafeInMaude.
To install CafeInMaude, we first need to intall Maude, which we can download its version 3.2 from here: http://maude.cs.illinois.edu/w/index.php/Maude_download_and_installation.
Both installations are simple, with Maude, you just need to download the binary file (and perhaps add the tool to the PATH environment variable to execute the tool from everywhere), while with CafeInMaude, you just need to clone its repo.
After that, move to the next step to execute proof scores.

## Executing proof scores
Proof scores are executable (CafeOBJ code).
Once intalled CafeInMaude, you can try to run a part of the proof score of `inv1` of the IFF protocol, which is a small example, by the following commands:

```
maude -allow-files path-to-CafeInMaude/src/cafeInMaude.maude
load IFF/iff.cafe .
load IFF/test.cafe .
```

where the first command starts the CafeInMaude environment (`path-to-CafeInMaude` is the path of the CafeInMaude folder),
the second command load the specification and the invariants, respectively,
and the last command loads the proof score.
If nothing is wrong, you will get the output result containing `Result: true : Bool`. 
Note that you need to make sure that the paths are correct. You may need to use the absolute paths instead of the relative paths as above.

After that, you do not need to load the specification again, but can continue loading the complete proof scores of `inv1` and `inv2`:

```
load IFF/proof-scores.cafe .
```

Moving to the Hybrid TLS protocol, similarly, you can run the proof of 
`ssKeySe` (the *session key secrecy* property) in the case client authentication is not requested by the following commands:

```
maude -allow-files path-to-CafeInMaude/src/cafeInMaude.maude
load without-client-authentication/hbtls-wtca.cafe .
load without-client-authentication/invariants.cafe .
load without-client-authentication/proof-ssKeySe.cafe .
```

Note that CafeInMaude may take 2-3 minutes to load the specification and the invariants (the second and third commands) due to their being large.
After that, you can continuously, for example, run the proof score of `pqKeySe` by the following command:

```
load without-client-authentication/gen-pqKeySe.cafe .
```

In this case, because the file is large, 
CafeInMaude may take around 1 minute to parse a proof score file before reducing the `red` commands.
Therefore, to reduce the time taken, a wise way is to split the file into some small sub-files and play with each of them. It will significantly reduce the time taken in total.

*Note also that* we can use CafeOBJ (https://cafeobj.org/) to execute the proof score (instead of CafeInMaude). But it may take a longer time since the rewriting system of the original CafeOBJ normally takes a longer amount of time to reduce a given term than that of CafeInMaude.
