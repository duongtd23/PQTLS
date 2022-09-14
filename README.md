## Symbolic verification of Hybrid Post-Quantum TLS 1.2.
---

In this repository, you can find:

1) IFF: IFF protocol specification in CafeOBJ, and its formal verification of the  *identifiable property* with proof scores.

2) without-client-authentication: The specification and verification of the Hybrid PQ TLS in case client authentication is **not** requested.
You will find the description of the contents of this folder and a detailed explanation of the formal specification in the readme file in this folder.

3) with-client-authentication: The specification and verification of the Hybrid PQ TLS in case client authentication is requested.
Similarly, you will find the description of the contents of this folder and a detailed explanation of the formal specification in the readme file in this folder.



## Tools installation
---
Our verification requires the use of CafeInMaude, which can be downloaded from here: https://github.com/ariesco/CafeInMaude.
To execute CafeInMaude, we first need to intall Maude, which we can download its version 3.2 from here: http://maude.cs.illinois.edu/w/index.php/Maude_download_and_installation.
After installing Maude, please follow the guide on CafeInMaude webpage to install it.

## Executing proof scores
---
Proof scores are executable (CafeOBJ code).
Once intalled CafeInMaude, you can try to run the proof score of `inv2` in the case client authentication is not requested by the following commands:

```
maude -allow-files path-to-CafeInMaude/src/cafeInMaude.maude
load without-client-authentication/hbtls-wtca.cafe .
load without-client-authentication/invariants.cafe .
load without-client-authentication/gen2.cafe .
```

where the first command starts the CafeInMaude environment (`path-to-CafeInMaude` is the path of the CafeInMaude folder),
the second and third commands load the specification and the invariants, respectively,
and the last command loads the proof score.
If nothing is wrong, you will get the output results containing `Result: true : Bool`. 
Note that you need to make sure that the paths are correct. You may need to use the absolute paths instead of the relative paths as above.

*Note also that* we can use CafeOBJ (https://cafeobj.org/) to execute the proof score (instead of CafeInMaude). But it may take a longer time since the rewriting system of the original CafeOBJ normally takes a longer amount of time to reduce a given term than that of CafeInMaude.
One more thing, CafeInMaude may take 1-2 minute(s) to parse a proof score file since that file is often very large, so to reduce the time taken, a wise way is to split the file into some small sub-files and play with each of them. It will significantly reduce the time taken in total.