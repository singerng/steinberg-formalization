# A formalization of Steinberg relations

A Lean verification of the lifting of Steinberg relations,
first proved by Noah Singer and Ryan O'Donnell in a [recent paper](https://arxiv.org/pdf/2411.05916).
The main theorem states that XYZ.


## Installing Lean

The main part of this repository is a mathematical formalization written in the Lean 4 theorem prover.
To install Lean on your machine,
see the [quickstart](https://lean-lang.org/lean4/doc/quickstart.html) guide from the Lean manual,
or [the extended setup instructions](https://lean-lang.org/lean4/doc/setup.html).


## Building the Lean formalization

Run:
```
lake exe cache get   # Downloads pre-built .olean files for mathlib
lake build           # Builds this project's main theorems
```

## Authors
- [Noah Singer](https://noahsinger.org/)
- [Cayden Codel?](https://crcodel.com)
