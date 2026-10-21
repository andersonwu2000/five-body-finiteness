# Lean development for five-body finiteness

Author and contact: Anderson Wu, andersonwu2000@gmail.com.

This project accompanies *Finiteness of Planar Central Configurations for Five Positive Masses*. See `REVIEW_CLOSURE.md` for the precise formal statement, definitions, verification scope, and manuscript correspondence. `Paper.lean` indexes numbered statements; `Check.lean` checks the main theorem and axiom dependencies.

Install elan and Git, then run from this directory:

```sh
lake exe cache get
lake build CentralConfigurations
lake env lean Check.lean
lake env lean Paper.lean
lake env leanchecker --fresh CentralConfigurations.FiveBody.D2Regular.PositiveFiniteness
```

Compiler and dependency revisions are pinned in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. The first build requires network access. The 391 source and configuration files match the recorded 9 October 2026 verification. Publication preparation did not rerun Lean.

AI agents produced the mathematical arguments and formalization under the author's coordination. An independent human expert review of the complete argument has not yet been completed.

## License

The source code and review documentation in this repository are distributed under the Apache License, Version 2.0. Dependencies retain their respective licenses.
