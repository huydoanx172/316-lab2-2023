# Overview

In this lab, you will start by developing a client application that produces evidence, in the form of authorization proofs, that a remote server should grant access to certain resources. As such, you will implement a theorem prover for the constructive authorization logic that we have discussed in lecture. However, your goal is not to implement a theorem prover that can prove *any* valid formula, but rather a limited set of formulas that make use of three authorization policies. To help you get started with this, a set of *tactics*, or modular techniques for making progress on finding proofs, are provided for you to work with and draw ideas from.

Having implemented the client, you will turn your attention to the authorization server, whose source is included in this repository. It contains a vulnerability, having to do with the way that it authenticates evidence sent by the client, that allows anyone to (erroneously) convince it that they should be granted access to *any* resource of their choice. You will identify the vulnerability, and demonstrate your understanding of it by implementing an exploit that causes the server to send you a credential to a forbidden resource.

## Learning goals

* Understand the core techniques that are used to automatically prove theorems like those needed for the authorization logic discussed in lecture.
* Gain experience designing customized automated reasoning techniques for specific instances of authorization policies.
* Develop familiarity with public-key authentication and how certificate authorities are used to establish trust.
* Gain experience identifying flaws in code that deals with authentication decisions, and developing exploits that leverage such flaws.

# Documentation

There is [detailed documentation](https://15316-cmu.github.io/lab2-2023/) for this lab to get you started. Before writing any code, read this documentation thoroughly and make a plan. Pay extra attention to the [Getting started](https://15316-cmu.github.io/lab2-2023/starter/) section of the docs!

# What to hand in

## Checkpoint

For the checkpoint, you do not need to submit your lab or hand code in. You just need to demonstrate that you have completed the first authorization goal by running `auth.py` and getting the credential from the authorization server:
```
$ python src/auth.py <your andrewid> <your andrewid.txt> -s
```
If you see output like the following, then you have successfully passed the checkpoint:
```
*********************************** Credential ***********************************
statement: open(#andrewid, <andrewid.txt>)
signator: #root
signature: [50:f0:40:3d:91:31:f3:ec:d2:99:bd:e6:b5:6c:8b:02]
**********************************************************************************
```

## Final submission

Submit your work on Gradescope. Create a `zip` archive of the repository, but make sure that you have not included the directory `lab1-2023` at the root of the archive. Additionally, there is no need to hand in test cases or files in `src/__pycache__`, and doing so may slow down processing by the autograder.

You are encouraged to use the `handin.sh` script, which will create an appropriate archive in `handin.zip` to upload to Gradescope. This script will not work when run from Windows' `cmd.exe` or Powershell, but you may translate it to use native Windows commands if you are not already using the WSL2 setup described at the top of this readme.

# Evaluation

This lab is worth 100 points, and will be graded by a combination of autograder test cases and, when necessary, manual inspection by the course staff. The test cases will use the same delegation policies described in this handout, but with a different set of credentials than those in this repository. We will also test your exploit in `exploit.py`, and ensure that the exploit is not used as a tactic by your prover.

The percentage breakdown is as follows.

* 25 points for a successful proof of `open(#andrewid, <andrewid.txt>)` (due by the checkpoint on 11/13)
* 25 points for a successful proof of `open(#andrewid, <shared.txt>)` (due on 11/21)
* 25 points for a successful proof of `open(#andrewid, <secret.txt>)` (due on 11/21)
* 25 points for an exploit that results in `open(#andrewid, <bigsecret.txt>)` (due on 11/21)

We will additionally check that the credentials used by your proofs for the top three bullets are minimal, i.e., that the access requests generated by your proofs do not send more credentials and certificates than are necessary to make the authorization claim. Proofs that use more credentials than are necessary will recieve 80% of the credit allotted by the corresponding bullet above.

If you miss the checkpoint deadline, but hand a solution for the checkpoint portion in with your submission on 11/21, then you will receive 3/4 of the points deducted at the checkpoint back.