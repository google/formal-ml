# Formal ML

<!--*
freshness: { owner: 'martinz' reviewed: '2020-08-13' }
*-->

## Introduction

Formal ML is a LEAN library for proving foundational results in measure
theory, probability, statistics, and machine learning, based upon mathlib.
It is in early development, and not all proofs are complete.

It introduces probability spaces, the Radon-Nikodym derivative, PAC bounds, etc.

The library can be used in other packages as well.


## Building the Package

This package is compatible with LEAN 3.20.0.


### Download and Install LEAN 3.20.0
This package is based upon the LEAN community version of lean, specifically version
3.20.0. Before building the package, one must download [LEAN 3.20.0](https://github.com/leanprover-community/lean/releases/tag/v3.20.0).

For Linux versions, you can download [https://github.com/leanprover-community/lean/releases/download/v3.20.0/lean-3.20.0-linux.tar.gz](https://github.com/leanprover-community/lean/releases/download/v3.20.0/lean-3.20.0-linux.tar.gz). After unzipping the
file, you can include the bin subdirectory in your PATH (no need to recompile).
To test your framework, run:

`lean --version`

`leanpkg help`

### Download FormalML

To download this package, run:

`git clone https://github.com/google/formal-ml.git`

`cd formal-ml`

### Build the Package
To build the package, run:

`leanpkg build`

This will download mathlib, and compile both mathlib and this package, so it may
take a few minutes.
