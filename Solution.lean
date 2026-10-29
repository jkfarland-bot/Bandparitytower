module

public import BandParityTower

public section

/-!
# Proved solution

Each declaration below has exactly the statement of its counterpart in `Challenge.lean` and is
proved from the development in `BandParityTower/`. The definitions used in the statements come from
`BandParityTower/Basic.lean`, `CosetSums.lean`, `Defs.lean`, `TowerDefs.lean` and `Mod8Defs.lean`,
and are compared with the copies in `Challenge.lean`.
-/

namespace BandParityTower

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The group `H_a` -/

/-- `H_a` has `m` elements; `2^a m = p - 1` with `m` odd; `H_a` is the group of nonzero `2^a`-th
powers, and `± H_a` the group of nonzero `2^{a-1}`-th powers. -/
theorem Ha_spec (hp2 : p ≠ 2) :
    (Ha p).card = oddPart p ∧ 2 ^ twoVal p * oddPart p = p - 1 ∧ Odd (oddPart p) ∧
      (∀ x : ZMod p, x ∈ Ha p ↔ x ≠ 0 ∧ ∃ y : ZMod p, y ^ 2 ^ twoVal p = x) ∧
      (∀ x : ZMod p, (x ≠ 0 ∧ ∃ y : ZMod p, y ^ 2 ^ (twoVal p - 1) = x) ↔ (x ∈ Ha p ∨ -x ∈ Ha p)) := by
  have h2 := prime_two_le (p := p)
  have ha : 1 ≤ twoVal p :=
    twoVal_pos (Nat.odd_iff.1 (odd_prime hp2)) (by have := hp.out.two_le; omega)
  refine ⟨card_Ha, two_pow_mul_oddPart h2, oddPart_odd h2, fun x => ?_, fun x => ?_⟩
  · by_cases hx : x = 0
    · subst hx; simp [zero_not_mem_Ha]
    · rw [exists_pow_top_iff hx, mem_Ha_iff]; simp [hx]
  · by_cases hx : x = 0
    · subst hx; simp [zero_not_mem_Ha]
    · rw [pm_Ha_iff hp2, ← exists_pow_pred_iff ha hx]; simp [hx]


/-! ### Section 4: the tower -/

/-- **Theorem 4.3 (the cyclotomic tower).** Let `g` be a primitive root, `K = 2^{a-1}`, and `χ` a
character with values in a commutative ring with `χ(g)^K = -1` (for instance the character of
order `2^a` with `χ(g) = e^{2πi/2^a}`). For even `e ≥ 2`, with `X_r = g^r H_a`,
`∑_{0 < n < p/2} χ(n) (-1)^{⌊n^e/p⌋} = ∑_{r < K} χ(g)^r T_r` and
`T_r ≡ m - 2α(X_r) - 2α(X_r^e) (mod 4)`, one congruence for each coordinate. -/
theorem cyclotomic_tower (hp2 : p ≠ 2) {g : ZMod p} (hg : orderOf g = p - 1) {R : Type*}
    [CommRing R] {χ : MulChar (ZMod p) R} (hζ : χ g ^ 2 ^ (twoVal p - 1) = -1) {e : ℕ}
    (he : Even e) (he0 : e ≠ 0) :
    bandSumPow χ e = ∑ r ∈ range (2 ^ (twoVal p - 1)),
        χ g ^ r * (pairBandSum (cosetOf (g ^ r) (Ha p)) e : R) ∧
      ∀ r : ℕ, pairBandSum (cosetOf (g ^ r) (Ha p)) e ≡
        (oddPart p : ℤ) - 2 * oddCountZ (cosetOf (g ^ r) (Ha p)) -
          2 * oddCountZ ((cosetOf (g ^ r) (Ha p)).image (· ^ e)) [ZMOD 4] :=
  cyclotomic_tower' hp2 hg hζ he he0

/-- **Corollary 4.4 (the band-parity tower).** For every odd prime,
`∑_{0 < n < p/2, n ∈ ± H_a} η(n) (-1)^{⌊n²/p⌋} = f_a ≡ m (mod 4)`, where `η` is the character of
`± H_a` with kernel `H_a`. -/
theorem band_parity_tower (hp2 : p ≠ 2) :
    ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p ∧ n ^ (2 * oddPart p) = 1),
        (if n ^ oddPart p = 1 then 1 else -1) * (-1 : ℤ) ^ band n = fTower p ∧
      fTower p ≡ oddPart p [ZMOD 4] :=
  ⟨towerBand_eq hp2, fTower_modEq hp2⟩

/-- **The doubling count** (Proposition 3.5 at `c = 2`). For `p ≡ 1 (mod 4)`,
`∑_{u ∈ 2H_a} s(u) s(2u) = 2N_a - m`. -/
theorem doubling_count (hp4 : p % 4 = 1) :
    ∑ u ∈ cosetOf 2 (Ha p), parSign u * parSign (2 * u) = 2 * (Na p : ℤ) - oddPart p :=
  lag_two hp4

/-- **Theorem 4.5.** For `p ≡ 1 (mod 4)`, the band-sum form
`∑_{0 < n < p/2, n ∈ ± 2H_a} σ(n) (-1)^{⌊n²/p⌋} = e_a` (`σ = ± 1` on `± 2H_a`), and
`e_a ≡ 2N_a - m (mod 4)`. -/
theorem imaginary_law (hp4 : p % 4 = 1) :
    ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p ∧ (n / 2) ^ (2 * oddPart p) = 1),
        (if (n / 2) ^ oddPart p = 1 then 1 else -1) * (-1 : ℤ) ^ band n = eTower p ∧
      eTower p ≡ 2 * (Na p : ℤ) - oddPart p [ZMOD 4] :=
  ⟨eTowerBand_eq (by omega), eTower_modEq hp4⟩

/-- **Corollary 4.6, level three.** For `p ≡ 9 (mod 16)` and either quartic character, with
`Ω = ∑_{0 < n < p/4} χ(n)`: `2(2N_3 - m) = κ + 2 Re Ω` and `2e_3 ≡ κ + 2 Re Ω (mod 8)`, that is,
`e_3 ≡ (κ + 2 Re Ω)/2 (mod 4)`. -/
theorem imaginary_law_three (hp16 : p % 16 = 9) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) :
    2 * (2 * (Na p : ℤ) - oddPart p) =
        kappa p + 2 * (∑ n ∈ (range p).filter (fun n => 0 < n ∧ 4 * n < p), χ (n : ZMod p)).re ∧
      2 * eTower p ≡
        kappa p + 2 * (∑ n ∈ (range p).filter (fun n => 0 < n ∧ 4 * n < p), χ (n : ZMod p)).re
        [ZMOD 8] :=
  elaw_three hp16 hχ

/-- **Corollary 4.7 (the collapse).** For `p ≡ 1 (mod 4)`, if `2` is a `2^{a-1}`-th power residue,
then `e_a = f_a` if `2 ∈ H_a` and `e_a = -f_a` otherwise, and `2` is a `2^a`-th power residue iff
`N_a` is odd. The last statement is E. Lehmer's Theorem 5 at `k = 2^{a-1}`
(see `lehmer_theorem_five`); here it is derived from the tower and the imaginary law. -/
theorem collapse_criterion (hp4 : p % 4 = 1) (h2 : ∃ y : ZMod p, y ^ 2 ^ (twoVal p - 1) = 2) :
    ((2 : ZMod p) ∈ Ha p → eTower p = fTower p) ∧
    ((2 : ZMod p) ∉ Ha p → eTower p = -fTower p) ∧
    ((∃ y : ZMod p, y ^ 2 ^ twoVal p = 2) ↔ Odd (Na p)) :=
  collapse hp4 h2

/-- **E. Lehmer, *Generalizations of Gauss's lemma* (1977), Theorem 5.** If `2k ∣ p - 1` and `2`
is a `k`-th power residue, then `2` is a `2k`-th power residue iff the number of `k`-th power
residues in `(0, p/4)` has the parity of `(p - 1)/(2k)`. -/
theorem lehmer_theorem_five {k : ℕ} (hk : 2 * k ∣ p - 1) (h2 : ∃ y : ZMod p, y ^ k = 2) :
    (∃ y : ZMod p, y ^ (2 * k) = 2) ↔ powResCount k p % 2 = ((p - 1) / (2 * k)) % 2 :=
  lehmer_criterion hk h2

/-- **Theorem 4.1 (the power-map family).** For `p ≡ 5 (mod 8)`, the quartic character with
`χ(2) = i`, `m ≥ 1`, `d = gcd(m, Q)` and `Θ_d = (-1)^{α(H) + α(H^d)}`:
`Re 𝒞_{2m} ≡ Q + 1 - Θ_d` and `Im 𝒞_{2m} ≡ (-1)^{m-1} (κ + 1 - Θ_d) (mod 4)`. -/
theorem power_map_family (hp8 : p % 8 = 5) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) (hpin : χ 2 = gi) {m : ℕ} (hm : 1 ≤ m) :
    (bandSumPow χ (2 * m)).re ≡ Q p + 1 - (-1) ^ (oddCountZ (Ha p) +
        oddCountZ ((Ha p).image (· ^ Nat.gcd m ((p - 1) / 4)))) [ZMOD 4] ∧
      (bandSumPow χ (2 * m)).im ≡ (-1) ^ (m - 1) * (kappa p + 1 - (-1) ^ (oddCountZ (Ha p) +
        oddCountZ ((Ha p).image (· ^ Nat.gcd m ((p - 1) / 4))))) [ZMOD 4] :=
  power_map_family' hp8 hχ hpin hm

/-- **Theorem 4.9 (the companion law at `p ≡ 1 (mod 8)`).** For either quartic character,
`Re 𝒞 ≡ Im 𝒞 ≡ κ (mod 4)`. (With `κ = h(-4p)/2` and Barrucand and Cohn, `𝒞 ≡ 0 (mod 4)` iff
`p = x² + 32y²`; neither of those classical inputs is formalized.) -/
theorem companion_law_one_mod_eight (hp8 : p % 8 = 1) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) :
    (bandSum χ).re ≡ kappa p [ZMOD 4] ∧ (bandSum χ).im ≡ kappa p [ZMOD 4] :=
  companion_one_mod_eight hp8 hχ

/-- **Theorem 4.11 (Lehmer-type invariants).** For `p ≡ 5 (mod 8)`, `p ≥ 13`, the pinned quartic
character and `n̄ = n⁻¹`: `E = #{1 ≤ n ≤ (p-1)/2 : ⟨n̄⟩ even} ≡ k + t ≡ κ - Q (mod 4)`, and
`𝓛 = ∑_{n ≤ (p-1)/2} χ(n) (-1)^{n + ⟨n̄⟩} ≡ -i β̄`, that is, `Re 𝓛 ≡ -t` and `Im 𝓛 ≡ -k (mod 4)`. -/
theorem lehmer_invariants (hp8 : p % 8 = 5) (hp5 : 5 < p) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) (hpin : χ 2 = gi) :
    ((univ.filter fun n : ZMod p => n ≠ 0 ∧ 2 * n.val < p ∧ Even (n⁻¹).val).card : ℤ) ≡
        k χ + t χ [ZMOD 4] ∧
      ((univ.filter fun n : ZMod p => n ≠ 0 ∧ 2 * n.val < p ∧ Even (n⁻¹).val).card : ℤ) ≡
        kappa p - Q p [ZMOD 4] ∧
      (∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p),
        χ n * (-1) ^ (n.val + (n⁻¹).val)).re ≡ -t χ [ZMOD 4] ∧
      (∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p),
        χ n * (-1) ^ (n.val + (n⁻¹).val)).im ≡ -k χ [ZMOD 4] :=
  lehmer_invariants' hp8 hp5 hχ hpin


/-! ### Section 5: modulo eight -/

/-- **Corollary 5.1 (the joint-parity form).** For `p ≡ 5 (mod 8)`, `p ≥ 13`:
`f = 4Δ(H) + 2k + 4t - Q` and `e = 4Δ(2H) - 3k - t - Q`. -/
theorem joint_parity_form (hp8 : p % 8 = 5) (hp5 : 5 < p) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) (hpin : χ 2 = gi) :
    (bandSum χ).re = 4 * jointOdd (Ha p) + 2 * k χ + 4 * t χ - Q p ∧
      (bandSum χ).im = 4 * jointOdd (cosetOf 2 (Ha p)) - 3 * k χ - t χ - Q p :=
  deltaForm' hp8 hp5 hχ hpin

/-- **Lemma 5.2.** For odd `k, t` and `h = (k² + t²)/2` (which is `h⁻` by the class number formula),
`h ≡ 1 + 4(ε(k) + ε(t)) (mod 8)` with `ε(x) = (x² - 1)/8 mod 2`, and `h ≡ 1 (mod 8)` iff
`k ≡ ± t (mod 8)`. -/
theorem hminus_mod_eight {k t : ℤ} (hk : Odd k) (ht : Odd t) :
    (k ^ 2 + t ^ 2) / 2 ≡ 1 + 4 * ((k ^ 2 - 1) / 8 % 2 + (t ^ 2 - 1) / 8 % 2) [ZMOD 8] ∧
      ((k ^ 2 + t ^ 2) / 2 ≡ 1 [ZMOD 8] ↔ k ≡ t [ZMOD 8] ∨ k ≡ -t [ZMOD 8]) :=
  hminus_modEq hk ht

/-- **Proposition 5.3 (the mod-8 dichotomy).** With `h = (k² + t²)/2`: if `κ ≡ Q (mod 4)` then
`k + t ≡ h - 1 (mod 8)`; otherwise `k + t ≡ 2 (mod 4)`, and if moreover `h ≡ 1 (mod 8)` then
`k ≡ t (mod 8)`. -/
theorem mod_eight_dichotomy (hp8 : p % 8 = 5) (hp5 : 5 < p) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) (hpin : χ 2 = gi) :
    (kappa p ≡ Q p [ZMOD 4] → k χ + t χ ≡ (k χ ^ 2 + t χ ^ 2) / 2 - 1 [ZMOD 8]) ∧
      (¬ kappa p ≡ Q p [ZMOD 4] → k χ + t χ ≡ 2 [ZMOD 4] ∧
        ((k χ ^ 2 + t χ ^ 2) / 2 ≡ 1 [ZMOD 8] → k χ ≡ t χ [ZMOD 8])) :=
  mod8_dichotomy' hp8 hp5 hχ hpin

/-- **Proposition 5.6 (1).** If squaring permutes a finite set `O` (for instance a cycle of `u ↦ u²`
on `H`), then `∑_{u ∈ O} s(u) s(u²) = |O| - 2 r_O` with `r_O` the number of sign changes, which is
even; so `O` contributes `|O|` modulo `4`. -/
theorem squaring_cycles {O : Finset (ZMod p)}
    (hO : Set.BijOn (fun x : ZMod p => x ^ 2) (O : Set (ZMod p)) (O : Set (ZMod p))) :
    ∑ u ∈ O, parSign u * parSign (u ^ 2) =
        O.card - 2 * (O.filter fun u => parSign u ≠ parSign (u ^ 2)).card ∧
      Even (O.filter fun u => parSign u ≠ parSign (u ^ 2)).card ∧
      ∑ u ∈ O, parSign u * parSign (u ^ 2) ≡ O.card [ZMOD 4] :=
  squaring_cycle' hO

/-- **Proposition 5.6 (2).** For a primitive cube root of unity `ω`, the cycle `{ω, ω²}`
contributes exactly `2`. -/
theorem cube_root_cycle (hp2 : p ≠ 2) {ω : ZMod p} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    parSign ω * parSign (ω ^ 2) + parSign (ω ^ 2) * parSign ((ω ^ 2) ^ 2) = 2 :=
  cube_root_pair' hp2 hω hω1

/-- For `p ≡ 5 (mod 8)`, `e = -∑_{h ∈ H} s(2h) s(P(h))` with `P(h) = -4h²` (Section 5.3). -/
theorem e_as_correlation (hp8 : p % 8 = 5) {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
    (hpin : χ 2 = gi) :
    (bandSum χ).im = -∑ h ∈ Ha p, parSign (2 * h) * parSign (-4 * h ^ 2) :=
  e_eq_neg_sum hp8 hχ hpin

/-- **Proposition 5.6 (3).** For `p ≡ 5 (mod 8)`, a primitive cube root `ω` and `x = ⟨ω⟩`, the
contribution `ρ₃ = -(s(2h₁) s(P h₁) + s(2h₂) s(P h₂))` to `e` of `h₁ = -ω/4`, `h₂ = -ω²/4`
(where `P h₁ = h₂` and `P h₂ = h₁`) is `0` if `x ≢ 2 (mod 4)`, `-2` if `x ≡ 2 (mod 8)` and `2` if
`x ≡ 6 (mod 8)`. -/
theorem order_three_pair (hp8 : p % 8 = 5) {ω : ZMod p} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    -(parSign (-ω / 2) * parSign (-ω ^ 2 / 4) + parSign (-ω ^ 2 / 2) * parSign (-ω / 4)) =
      if ω.val % 4 ≠ 2 then 0 else if ω.val % 8 = 2 then -2 else 2 :=
  rho_three' hp8 hω hω1

/-- For `p ≡ 5 (mod 8)`, `f = Re 𝒞` is the tower coordinate `f_2`. -/
theorem real_part_eq_fTower (hp8 : p % 8 = 5) {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4) :
    (bandSum χ).re = fTower p := by rw [bandSum_re' hχ hp8, cls_one_eq hχ hp8]; rfl

/-- **Lemma 5.7 (first identity).** `M_H(a) = m - 4α + 4C(a)` for `a ∈ H`. -/
theorem multiplier_identity {a : ZMod p} (ha : a ∈ Ha p) :
    multCorr a = oddPart p - 4 * oddCountZ (Ha p) + 4 * multCount a :=
  multCorr_eq' ha

/-- **Lemma 5.7 (second identity).** `∑_{a ∈ H} C(a) = α²`. -/
theorem multiplier_count_sum : ∑ a ∈ Ha p, (multCount a : ℤ) = (oddCountZ (Ha p) : ℤ) ^ 2 :=
  sum_multCount'

/-- **Lemma 5.7 (the defect congruence).** `2(f_a - m) ≡ ∑_{a ∈ H, a ≠ a⁻¹} d(a)(M_H(a) - m)
(mod 16)`. Each pair `{a, a⁻¹}` is counted from both ends, and the summand is the same at `a`
and `a⁻¹`, so this is the paper's `f ≡ Q + ∑_{{a, a⁻¹}} d(a)(M_H(a) - Q) (mod 8)` at
`p ≡ 5 (mod 8)`; it holds at every odd prime. -/
theorem defect_congruence (hp2 : p ≠ 2) :
    2 * (fTower p - oddPart p) ≡ ∑ a ∈ (Ha p).filter (fun a => a ≠ a⁻¹),
      defect a * (multCorr a - oddPart p) [ZMOD 16] :=
  defect_lemma' hp2

/-- **Proposition 5.8 (odd multipliers are floor sums).** For `p ≡ 5 (mod 8)` and odd `a > 0`
prime to `p`, `M_H(a) = ∑_{u ∈ H} (-1)^{⌊a⟨u⟩/p⌋} = ¼ ∑_{0 < n < p} (1 + (n/p)) (-1)^{⌊an/p⌋}`. -/
theorem odd_multipliers (hp8 : p % 8 = 5) {a : ℕ} (ha : Odd a) (hpa : ¬ p ∣ a) :
    multCorr (a : ZMod p) = ∑ u ∈ Ha p, (-1 : ℤ) ^ (a * u.val / p) ∧
      4 * multCorr (a : ZMod p) = ∑ n ∈ (range p).filter (0 < ·),
        (1 + legendreSym p n) * (-1) ^ (a * n / p) :=
  odd_multiplier' hp8 ha hpa

/-- **Theorem 5.9 (the fifth-interval formula).** Let `p ≡ 29 (mod 40)`, `v = (p + 1)/5`, `R_5(p)`
the number of quadratic residues in `(p/5, 2p/5)`, `θ_p = (·/p) ξ` with `ξ` the quartic character
modulo `5` with `ξ(2) = i`, and `B_{1,θ_p} = R + i I`. Then `R`, `I` are integers,
`R_5 = (2v + I - R)/4`, `M_H(5) = Q - v + (R - I)/2`; `5 ∈ H` iff `R - I ≡ 2v (mod 8)`; and then the
pair `{5, 5⁻¹}` contributes `4` modulo `8` to the sum of Lemma 5.7 iff `R - I ≡ 2v - 8 (mod 16)`. -/
theorem fifth_interval_formula (hp40 : p % 40 = 29) :
    ((5 * p : ℕ) : ℤ) ∣ (thetaSum p).re ∧ ((5 * p : ℕ) : ℤ) ∣ (thetaSum p).im ∧
      4 * (fifthCount p : ℤ) = 2 * ((p + 1) / 5 : ℕ) + (thetaSum p).im / (5 * p : ℕ) -
        (thetaSum p).re / (5 * p : ℕ) ∧
      2 * multCorr (5 : ZMod p) = 2 * Q p - 2 * ((p + 1) / 5 : ℕ) +
        (thetaSum p).re / (5 * p : ℕ) - (thetaSum p).im / (5 * p : ℕ) ∧
      ((5 : ZMod p) ∈ Ha p ↔ (thetaSum p).re / (5 * p : ℕ) - (thetaSum p).im / (5 * p : ℕ) ≡
        2 * ((p + 1) / 5 : ℕ) [ZMOD 8]) ∧
      ((5 : ZMod p) ∈ Ha p →
        (defect (5 : ZMod p) * (multCorr (5 : ZMod p) - Q p) ≡ 4 [ZMOD 8] ↔
          (thetaSum p).re / (5 * p : ℕ) - (thetaSum p).im / (5 * p : ℕ) ≡
            2 * ((p + 1) / 5 : ℕ) - 8 [ZMOD 16])) :=
  fifth_interval hp40

end BandParityTower
