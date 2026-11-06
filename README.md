# LCS-Bench: Lean 4 Formalization of *Logic for Computer Science*

Lean 4 artifact of LCS-Bench, accompanying the NeurIPS 2026 Evaluations &
Datasets Track paper *Theory-Scale Auto-Formalization of Logic for Computer
Science*. The library formalizes Jean H. Gallier's *Logic for Computer
Science: Foundations of Automatic Theorem Proving* (second edition):
propositional logic, first-order logic, Gentzen systems (LK / LKe), cut
elimination, resolution, Herbrand's theorem, and SLD resolution.

The benchmark dataset generated from this library, with the DefEq checker and
the evaluation harness, is hosted separately on Kaggle:
https://www.kaggle.com/datasets/macaroonotz/lcs-bench

## Build

```bash
lake build
```

The Lean toolchain is pinned in `lean-toolchain` (Lean 4 v4.35.0).
Dependencies are the vendored packages in `vendor/` (LeanArchitect, Attach);
Lake fetches their dependencies (Batteries, lean4-cli) as pinned in
`lake-manifest.json`.

## Layout

- `LCS.lean`: top-level aggregator that imports every module.
- `LCS/`: library source, organised by topic:
  - `Propositional/`: propositional syntax, semantics, Gentzen systems.
  - `FirstOrder/`: first-order syntax, semantics, completeness, equality.
  - `CutElim/`: cut elimination (Hauptsatz, Beth, interpolation), LK, LKe.
  - `Resolution/`, `FOResolution/`: propositional and first-order resolution.
  - `Herbrand/`: Herbrand's theorem.
  - `SLD/`: SLD resolution and logic programming.
  - `Util.lean`, `Item.lean`: shared utilities and textbook item tagging.
- `attached_units.txt`: registry of modules whose proofs are kept in separate `Proofs.lean` files.
- `vendor/`: vendored Lean packages.

Theorems tagged `@[attach_debt]` have proofs that still contain `sorry`.
`ATTACH-BLOCKER` comments record why a helper declaration stays in a module
instead of its `Proofs.lean` file.

## Authors

Yuming Feng (Johns Hopkins University), Frederick Pu (University of Toronto),
One An (University of Pennsylvania), Osbert Bastani (University of Pennsylvania),
Li Zhang (Drexel University), Jiani Huang (University of Pennsylvania),
Xujie Si (University of Toronto), Ziyang Li (Johns Hopkins University).

## Citation

```bibtex
@inproceedings{feng2026lcsbench,
  title     = {Theory-Scale Auto-Formalization of Logic for Computer Science},
  author    = {Feng, Yuming and Pu, Frederick and An, One and Bastani, Osbert and
               Zhang, Li and Huang, Jiani and Si, Xujie and Li, Ziyang},
  booktitle = {Advances in Neural Information Processing Systems,
               Evaluations and Datasets Track},
  year      = {2026}
}
```

## License

MIT for the LCS library; see `LICENSE`. `vendor/LeanArchitect` is distributed
under its own Apache 2.0 license (`vendor/LeanArchitect/LICENSE`).
