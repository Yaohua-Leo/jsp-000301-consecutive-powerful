# JSP-000301 — Consecutive powerful numbers without a square

Lean 4 formalization of a counterexample to the following question from the
Justin Sun Prize problem bank, record **JSP-000301**:

> If two consecutive positive integers are powerful, must at least one be a
> perfect square?

The answer is **no**. The witness is the pair

- `12167 = 23^3`
- `12168 = 2^3 * 3^2 * 13^2`

Both are powerful, they are consecutive, and neither is a perfect square. The
formalization below proves the negation of the stated question.

## Theorem index

| Theorem | Statement |
| --- | --- |
| `JSP301.powerful_12167` | `Powerful 12167` |
| `JSP301.powerful_12168` | `Powerful 12168` |
| `JSP301.not_square_12167` | `¬ IsSquare (12167 : ℕ)` |
| `JSP301.not_square_12168` | `¬ IsSquare (12168 : ℕ)` |
| `JSP301.jsp301_counterexample` | `∃ n : ℕ, 0 < n ∧ Powerful n ∧ Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1)` |
| `JSP301.jsp301_false` | `¬ (∀ n : ℕ, 0 < n → Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1))` |

`Powerful` is defined locally: `n` is a positive integer such that every prime
`p` dividing `n` satisfies `p ^ 2 ∣ n`. Squares use mathlib's standard
`IsSquare`, which for `ℕ` means `∃ r, n = r * r`.

## Proof outline

- `powerful_12167`: every prime divisor of `23 ^ 3` divides `23 ^ 3`, hence
  equals `23`; `23 ^ 2 ∣ 12167` with cofactor `23`.
- `powerful_12168`: a prime divisor of `2 ^ 3 * 3 ^ 2 * 13 ^ 2` equals `2`, `3`
  or `13`; each square divides `12168` with cofactor `3042`, `1352` and `72`
  respectively.
- `not_square_12167` and `not_square_12168`: both numbers lie strictly between
  `110 ^ 2 = 12100` and `111 ^ 2 = 12321`. The auxiliary lemma
  `not_square_of_sq_lt_and_lt_sq` rules out an arbitrary candidate square root
  in that interval, rather than checking finitely many roots.
- `jsp301_counterexample` and `jsp301_false`: the two powerfullness results and
  the two non-square results are combined, with no additional hypotheses.

## Files

| File | Purpose |
| --- | --- |
| `Counterexample.lean` | The formalization: the definition, two auxiliary lemmas, and the six theorems. |
| `StatementAudit.lean` | Restatement checks written against expanded forms of the claims, plus an axiom audit for each theorem. |
| `lakefile.toml` | Lake package definition, with the mathlib revision pinned. |
| `lean-toolchain` | Pinned Lean toolchain. |

## Build

Requires [elan](https://github.com/leanprover/elan) and network access for the
first build.

```sh
lake update
lake exe cache get
lake build
lake env lean StatementAudit.lean
```

`StatementAudit.lean` prints the axioms each theorem depends on. All six depend
only on `propext`, `Classical.choice` and `Quot.sound`. The proof contains no
`sorry`, `admit`, added axiom, `native_decide`, `unsafe` or `implemented_by`.

Toolchain used for the archived build:

- Lean `4.29.0-rc6`, commit `00659f8e6071d7e46131ed643bf8003b99b044e9`
- mathlib commit `a40f85dba285155aaaca032f3451769c6d826d50`

## Scope and attribution

- The counterexample is not new. It is a known result in the literature on
  powerful numbers, cited in the JSP-000301 record as Golomb (1970) and
  Walker (1976). This repository formalizes that known counterexample; it claims
  no new mathematical discovery.
- This repository addresses the yes/no question quoted above and nothing else.
  It does not settle the separate counting question of Erdős problem #365.
- Formalization credit for this repository follows repository ownership.

## License

MIT. See [LICENSE](LICENSE).
