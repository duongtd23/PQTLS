## How to re-generate the proof scores

First, we need to install the IPSG tool. The tool can be found at this repo: https://github.com/duongtd23/IPSG-tool. From that webpage, you can see the installation guide, however, the tool can be easily installed by just cloning the repo since you must have already installed Maude. You should first test with the example commands shown on its README.

Once you have successfully installed IPSG, you can execute it to re-generate the proof scores of the Hybrid TLS case study.
For example, to generate the proof score for `inv2` in case client authentication is not requested, we use the following commands:

```
maude -allow-files path-to-IPSG-tool/ipsg.maude
load without-client-authentication/hbtls-wtca.cafe .
load without-client-authentication/invariants.cafe .
load without-client-authentication/inputs/invput2.cafe .
```

where the first command starts the tool (`path-to-IPSG-tool` is the path of the IPSG-tool folder you have just cloned).
The second and third load commands load the CafeOBJ specification and invariants, respectively.
The last command loads the input file `input2.cafe`, which asks the tool to generate the proof score for `inv2`.
Note that, for the second and third commands, CafeInMaude may take 2-3 minutes to load the specification and the invariants.
Recall that IPSG is implemented on top of CafeInMaude.
After that, you do not need to load the specification or the invariants again, but you can continuously ask the tool to generate proof scores for the other invariants.
For example, you can continuously ask the tool to generate the proof score for `inv3`:

```
load without-client-authentication/inputs/invput3.cafe .
```