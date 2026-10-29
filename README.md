# BandParityTower

Lean 4 / Mathlib formalization of the tower and the analysis modulo 8 in J. S. Farland,
*The band-parity companion of a quartic L-value: a congruence law, its tower, and its limit
modulo eight* (Paper I, Sections 4 and 5). It continues
[BandParity](https://github.com/jkfarland-bot/bandparity)
([doi:10.5281/zenodo.23673067](https://doi.org/10.5281/zenodo.23673067)), which formalized
Theorem A, the matching lemma, the lag identity at level 4, the Coordinate Congruence and the
odd-subgroup congruence (Theorem B).

For a prime `p` write `a = v₂(p - 1)`, `m = (p - 1)/2^a`, `H_a` for the subgroup of `(ℤ/p)ˣ` of
order `m`, `s(x) = (-1)^⟨x⟩`, and

  `f_a = ∑_{u ∈ H_a} s(u) s(u²)`,  `e_a = ∑_{u ∈ 2H_a} s(u) s(u²)`,
  `N_a = #{0 < n < p/4 : n is a 2^{a-1}-th power residue}`.

This repository proves:

- **The cyclotomic tower** (Theorem 4.3). For the character of order `2^a`, the band-parity sum
  `∑_{0<n<p/2} χ(n)(-1)^{⌊n^e/p⌋}` is `∑_r χ(g)^r T_r` exactly, with
  `T_r ≡ m - 2α(g^r H_a) - 2α((g^r H_a)^e) (mod 4)`: one congruence for each coordinate.
- **The band-parity tower** (Corollary 4.4). `f_a ≡ m (mod 4)` at every odd prime.
- **The doubling count.** `∑_{u ∈ 2H_a} s(u) s(2u) = 2N_a - m` for `p ≡ 1 (mod 4)`, by a direct
  count (the case `c = 2` of Proposition 3.5).
- **The imaginary law at every level** (Theorem 4.5). `e_a ≡ 2N_a - m (mod 4)`; at
  `p ≡ 9 (mod 16)`, `2e_3 ≡ κ + 2 Re Ω (mod 8)` with `Ω = ∑_{0<n<p/4} χ₄(n)` (Corollary 4.6).
- **The collapse** (Corollary 4.7). If `2` is a `2^{a-1}`-th power residue, `e_a = ± f_a`
  according as `2 ∈ H_a`, and `2` is a `2^a`-th power residue iff `N_a` is odd.
- **E. Lehmer's criterion** (*Generalizations of Gauss's lemma*, 1977, Theorem 5): if
  `2k ∣ p - 1` and `2` is a `k`-th power residue, then `2` is a `2k`-th power residue iff the
  number of `k`-th power residues in `(0, p/4)` has the parity of `(p - 1)/(2k)`. This is a
  classical input; the collapse gives a second proof at `k = 2^{a-1}`.
- **The power-map family** (Theorem 4.1), **the companion law at `p ≡ 1 (mod 8)`**
  (`Re 𝒞 ≡ Im 𝒞 ≡ κ`, Theorem 4.9) and **Lehmer-type invariants** of the inversion map
  (`E ≡ k + t ≡ κ - Q` and `𝓛 ≡ -i β̄ (mod 4)`, Theorem 4.11).
- **Modulo 8.** The joint-parity form (Corollary 5.1), Lemma 5.2, the mod-8 dichotomy
  (Proposition 5.3), squaring cycles and the order-three pair (Proposition 5.6), the defect
  lemma (Lemma 5.7), odd multipliers as floor sums (Proposition 5.8), and the fifth-interval
  formula (Theorem 5.9).

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

```
lake exe cache get
lake build
```

No `sorry`, no `native_decide`. Every result depends only on `propext`, `Classical.choice` and
`Quot.sound`. The comparator accepts `Solution.lean` against `Challenge.lean` on the Lean kernel,
nanoda and con-ron.

## Scope, hypotheses and limitations

- `H_a` is the set `{x : x^m = 1}` in `ZMod p`, and cosets are images `cosetOf c S = c S`.
  `Ha_spec` proves that `H_a` has `m` elements, is the group of nonzero `2^a`-th powers, and that
  `± H_a` is the group of nonzero `2^{a-1}`-th powers.
- In the cyclotomic tower the character takes values in any commutative ring with
  `χ(g)^{2^{a-1}} = -1` for a primitive root `g`. This covers the character of order `2^a` with
  `χ(g) = e^{2πi/2^a}`. "One congruence for each coordinate" is the exact identity
  `𝒞 = ∑_r χ(g)^r T_r` together with a congruence for each `T_r`; that `1, ζ, …, ζ^{2^{a-1}-1}`
  is a basis of `ℤ[ζ]` is not formalized.
- `κ` is the Legendre sum over `(0, p/4)`. Dirichlet's identification `κ = h(-4p)/2`, Barkan's
  quarter twist (the Bernoulli form of Corollary 4.6), Barrucand and Cohn's criterion (the last
  sentence of Theorem 4.9), and the class-number readings of `h⁻` and of Paper IV's thresholds
  (Remark 4.8) are quoted in the paper and not formalized. Lemma 5.2 and Proposition 5.3 are
  stated for `h = (k² + t²)/2`, which is `h⁻` by the class number formula.
- The defect lemma is stated with each pair `{a, a⁻¹}` counted from both ends: the sum runs over
  all `a ∈ H` with `a ≠ a⁻¹`, the summand is the same at `a` and `a⁻¹`, and the congruence is
  doubled to modulus 16. It is proved at every odd prime, with `m` in place of `Q`; the paper
  states it at `p ≡ 5 (mod 8)`.
- Proposition 5.6 (1) is proved for any finite set on which squaring is a bijection, so in
  particular for each squaring cycle.
- The witness propositions (Proposition 3.9, completeness modulo 4, and Proposition 5.4, no
  refinement modulo 8) are finite computations and are not formalized; neither are the
  observations.

## Sources and novelty

E. Lehmer's Theorem 5 is classical and is formalized here as an input; its case `k = 2` is the
criterion of Williams and Currie. The rung `a = 1` of the band-parity tower is classical (Sun 2019,
Corollary 1.1). The evaluation of `R_5(p)` through `B_{1,θ_p}` in Theorem 5.9 is of classical
Lerch / Johnson–Mitchell type; what is new there is the link to `M_H(5)`. The author found the
remaining results nowhere in the literature searched (see `formalization.yaml`); novelty is
claimed only relative to that search.

## Authorship, AI assistance and licence

The mathematics, the statements and the paper are by Joseph S. Farland. The Lean code was drafted
and repaired by Claude (Anthropic) against the paper's statements and proofs. Several proofs take
shorter routes than the paper (for example the inversion-map invariants and the fifth-interval
parity). The code is released under the Apache License 2.0 (`LICENSE`); the paper is CC BY 4.0.

## Layout for the Palomar registry

- `Challenge.lean` is the statement surface to audit. It restates the definitions exactly as the
  development has them and states the 24 results with `sorry`.
- `Solution.lean` proves the same declarations from the development in `BandParityTower/`.
- `comparator.json` lists the compared theorems and definitions and the permitted axioms.
- `formalization.yaml` records authorship, sources, AI assistance, scope and fidelity.
- `scripts/` holds Palomar's checks, copied from the Palomar starter template.

```
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh      # needs bubblewrap (bwrap)
```

| Paper I | Challenge declaration |
|---|---|
| Section 3.3, `H_a` and power residues | `Ha_spec` |
| Proposition 3.5 at `c = 2` | `doubling_count` |
| Theorem 4.1 | `power_map_family` |
| Theorem 4.3 | `cyclotomic_tower` |
| Corollary 4.4 | `band_parity_tower` |
| Theorem 4.5 | `imaginary_law` |
| Corollary 4.6 (`a = 3`) | `imaginary_law_three` |
| Corollary 4.7 | `collapse_criterion` |
| E. Lehmer 1977, Theorem 5 (Remark 4.8) | `lehmer_theorem_five` |
| Theorem 4.9 | `companion_law_one_mod_eight` |
| Theorem 4.11 | `lehmer_invariants` |
| Corollary 5.1 | `joint_parity_form`, `real_part_eq_fTower` |
| Lemma 5.2 | `hminus_mod_eight` |
| Proposition 5.3 | `mod_eight_dichotomy` |
| Proposition 5.6 | `squaring_cycles`, `cube_root_cycle`, `e_as_correlation`, `order_three_pair` |
| Lemma 5.7 | `multiplier_identity`, `multiplier_count_sum`, `defect_congruence` |
| Proposition 5.8 | `odd_multipliers` |
| Theorem 5.9 | `fifth_interval_formula` |

## Files

| File | Contents |
|---|---|
| `Basic`, `Pin`, `FixedBase`, `CosetSums`, `Defs`, `Matching`, `Laws`, `Main`, `OddSubgroup` | BandParity v1.0, renamed into the `BandParityTower` namespace |
| `TowerDefs`, `Mod8Defs` | definitions of the tower and of Section 5 |
| `Group` | counting roots of unity, the power residue criterion, `a` and `m` |
| `Half` | sums over half-systems, the representative identity, the odd-subgroup congruence for `H_a` |
| `Tower` | Corollary 4.4, the doubling count, Theorem 4.5, Corollary 4.7 |
| `Lehmer` | E. Lehmer's Theorem 5 |
| `Quartic` | quartic characters and fourth powers, Corollary 4.6 |
| `Cyclo` | Theorem 4.3 |
| `PowerMap` | Theorem 4.1 |
| `OneMod8` | Theorem 4.9 |
| `Inversion` | Theorem 4.11 |
| `Mod8` | Corollary 5.1, Lemma 5.2, Proposition 5.3 |
| `Cycles` | Proposition 5.6 |
| `Defect` | Lemma 5.7, Proposition 5.8 |
| `Fifth` | Theorem 5.9 |
