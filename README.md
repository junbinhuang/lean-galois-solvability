# galois-solvability

A Lean 4 formalization of Galois's solvability-by-radicals criterion over fields
of characteristic zero, built on mathlib:

> A polynomial is solvable by radicals if and only if its Galois group is solvable.

The project extends mathlib's existing necessary direction with the converse
and reusable results on finite radical towers and splitting fields.

The main theorem is
`Polynomial.solvableByRadicals_iff_isSolvable_gal`, available through
`import Galois`. Here, solvability by radicals means splitting in a finite
radical extension, which may be larger than the splitting field.

## Build

Lean and mathlib versions are pinned in the project files.
With elan installed, run these commands from the project root:

```bash
lake exe cache get
lake build
lake env lean Verification.lean
```

The `.lake/` directory is generated locally and is not tracked by Git.

## References

- Ian Stewart. *Galois Theory*. 5th ed. Chapman & Hall/CRC, 2022.
  [doi:10.1201/9781003213949](https://doi.org/10.1201/9781003213949).
- [mathlib4](https://github.com/leanprover-community/mathlib4), especially
  `Mathlib.FieldTheory.AbelRuffini` and `Mathlib.FieldTheory.KummerExtension`.

Licensed under Apache 2.0; see [LICENSE](LICENSE).

## Review and upstreaming

This project was developed with AI assistance. We will conduct rigorous human
review and revision of all statements and proofs, align the code with mathlib's
standards, and submit suitable results as focused pull requests with the goal
of inclusion in mathlib, subject to community review.
