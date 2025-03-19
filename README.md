# A formalization of Steinberg relations

A Lean verification of the lifting of Steinberg relations,
first proved by Noah Singer and Ryan O'Donnell in a [recent paper](https://arxiv.org/pdf/2411.05916).
The main theorem states that a strict subset of the Steinberg relations imply the rest.


## Installing Lean

The main part of this repository is a mathematical formalization written in the Lean 4 theorem prover.
To install Lean on your machine,
see the [quickstart](https://lean-lang.org/lean4/doc/quickstart.html) guide from the Lean manual,
or [the extended setup instructions](https://lean-lang.org/lean4/doc/setup.html).
For development,
we recommend using the Lean 4 [VS Code extension](https://github.com/leanprover/vscode-lean4).


## Building the Lean formalization

At the root of this project, run:
```bash
lake exe cache get   # Downloads pre-built .olean files for mathlib
lake build           # Builds this project's main theorems
```

## License

This project is licensed under the Apache 2.0 license (see [LICENSE](LICENSE)).
The "Steinberg Group" refers to the authors/contributors listed below.

## Authors and contributors

- [Noah Singer](https://noahsinger.org/), a PhD student at Carnegie Mellon University
- [Cayden Codel](https://crcodel.com), a PhD student at Carnegie Mellon University
- Eric Wang, an undergraduate at Carnegie Mellon University
- Arohee Bhoja, an undergraduate at Carnegie Mellon University
