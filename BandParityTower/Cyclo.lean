module

public import BandParityTower.Tower

@[expose] public section

/-!
# The cyclotomic tower (Theorem 4.3)

Let `g` be a primitive root modulo `p`, `K = 2^{a-1}`, and `χ` a character with values in a
commutative ring `R` with `χ(g)^K = -1` (for instance the character of order `2^a` with
`χ(g) = e^{2πi/2^a}`). For even `e ≥ 2` and `X_r = g^r H_a`,

  `∑_{0 < n < p/2} χ(n) (-1)^{⌊n^e/p⌋} = ∑_{r < K} χ(g)^r T_r`,
  `T_r ≡ m - 2α(X_r) - 2α(X_r^e) (mod 4)`,

where `T_r` is the band-parity sum of the pair of cosets `X_r ∪ (-X_r)`. Read in the basis
`1, ζ, …, ζ^{K-1}` of `ℤ[ζ]`, this is one congruence modulo `4` for each coordinate.
-/

namespace BandParityTower

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

section Generator

variable {g : ZMod p} (hg : orderOf g = p - 1)
include hg

lemma gen_pow_eq_one_iff (j : ℕ) : g ^ j = 1 ↔ p - 1 ∣ j := by
  rw [← hg, orderOf_dvd_iff_pow_eq_one]

lemma gen_ne_zero : g ≠ 0 := by
  rintro rfl
  have h1 := (gen_pow_eq_one_iff hg (p - 1)).2 dvd_rfl
  have : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  rw [zero_pow this] at h1
  exact zero_ne_one h1

lemma gen_pow_eq_pow_iff {i j : ℕ} : g ^ i = g ^ j ↔ i ≡ j [MOD p - 1] := by
  wlog hij : i ≤ j generalizing i j
  · rw [eq_comm, Nat.ModEq.comm]; exact this (by omega)
  have hgi : g ^ i ≠ 0 := pow_ne_zero _ (gen_ne_zero hg)
  have : g ^ j = g ^ i * g ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij]
  rw [this, eq_comm, mul_eq_left₀ hgi, gen_pow_eq_one_iff hg, Nat.modEq_iff_dvd' hij]

lemma gen_surj (x : ZMod p) (hx : x ≠ 0) : ∃ j : ℕ, g ^ j = x := by
  have hp1 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  have hsub : (range (p - 1)).image (g ^ ·) = univ.filter (fun y : ZMod p => y ≠ 0) := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      obtain ⟨j, -, rfl⟩ := mem_image.1 hy
      simp [gen_ne_zero hg]
    · rw [card_image_of_injOn, card_range]
      · have : (univ.filter fun y : ZMod p => y ≠ 0) = univ.erase 0 := by ext; simp
        rw [this, card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
      · intro i hi j hj h
        simp only [coe_range, Set.mem_Iio] at hi hj
        have := (gen_pow_eq_pow_iff hg).1 h
        exact Nat.ModEq.eq_of_lt_of_lt this hi hj
  have : x ∈ (range (p - 1)).image (g ^ ·) := by rw [hsub]; simpa using hx
  obtain ⟨j, -, hj⟩ := mem_image.1 this
  exact ⟨j, hj⟩

end Generator

section Tower

variable (hp2 : p ≠ 2) {g : ZMod p} (hg : orderOf g = p - 1)
include hp2 hg

/-- With `n = g^j`, `n ∈ ± g^r H_a` exactly when `j ≡ r (mod 2^{a-1})`. -/
lemma pm_coset_gen_iff (r j : ℕ) :
    (g ^ j ∈ cosetOf (g ^ r) (Ha p) ∨ -g ^ j ∈ cosetOf (g ^ r) (Ha p)) ↔
      j ≡ r [MOD 2 ^ (twoVal p - 1)] := by
  have hg0 := gen_ne_zero hg
  have ha := twoVal_pos (Nat.odd_iff.1 (odd_prime hp2)) (by have := hp.out.two_le; omega)
  have hK := two_pow_pred_mul (prime_two_le (p := p)) ha
  rw [pm_coset_iff hp2 (pow_ne_zero _ hg0), mul_pow, inv_pow, inv_mul_eq_one₀
    (pow_ne_zero _ (pow_ne_zero _ hg0)), ← pow_mul, ← pow_mul, gen_pow_eq_pow_iff hg, ← hK]
  have hm0 : 2 * oddPart p ≠ 0 := by have := oddPart_pos (prime_two_le (p := p)); omega
  exact ⟨fun h => (Nat.ModEq.mul_right_cancel' hm0 h).symm,
    fun h => Nat.ModEq.mul_right' _ h.symm⟩

lemma exists_unique_index {n : ZMod p} (hn : n ≠ 0) :
    ∃ r ∈ range (2 ^ (twoVal p - 1)),
      (n ∈ cosetOf (g ^ r) (Ha p) ∨ -n ∈ cosetOf (g ^ r) (Ha p)) ∧
      ∀ r' ∈ range (2 ^ (twoVal p - 1)),
        (n ∈ cosetOf (g ^ r') (Ha p) ∨ -n ∈ cosetOf (g ^ r') (Ha p)) → r' = r := by
  obtain ⟨j, rfl⟩ := gen_surj hg n hn
  refine ⟨j % 2 ^ (twoVal p - 1), mem_range.2 (Nat.mod_lt _ (by positivity)),
    (pm_coset_gen_iff hp2 hg _ _).2 (Nat.mod_modEq _ _).symm, fun r' hr' h => ?_⟩
  have := (pm_coset_gen_iff hp2 hg _ _).1 h
  exact (Nat.ModEq.eq_of_lt_of_lt (this.symm.trans (Nat.mod_modEq _ _).symm)
    (mem_range.1 hr') (Nat.mod_lt _ (by positivity)))

variable {R : Type*} [CommRing R] {χ : MulChar (ZMod p) R}
  (hζ : χ g ^ 2 ^ (twoVal p - 1) = -1)
include hζ

lemma char_of_mem_Ha {h : ZMod p} (hh : h ∈ Ha p) : χ h = 1 := by
  have hg0 := gen_ne_zero hg
  obtain ⟨j, rfl⟩ := gen_surj hg h (ne_zero_of_mem_Ha hh)
  rw [mem_Ha_iff, ← pow_mul, gen_pow_eq_one_iff hg,
    ← two_pow_mul_oddPart (prime_two_le (p := p))] at hh
  obtain ⟨q, hq⟩ : 2 ^ twoVal p ∣ j := Nat.dvd_of_mul_dvd_mul_right
    (oddPart_pos (prime_two_le (p := p))) hh
  have ha := twoVal_pos (Nat.odd_iff.1 (odd_prime hp2)) (by have := hp.out.two_le; omega)
  have h2a : χ g ^ 2 ^ twoVal p = 1 := by
    rw [show twoVal p = twoVal p - 1 + 1 by omega, pow_succ, pow_mul, hζ]; norm_num
  rw [map_pow, hq, pow_mul, h2a, one_pow]

lemma char_neg_one : χ (-1) = -1 := by
  have hg0 := gen_ne_zero hg
  have ha := twoVal_pos (Nat.odd_iff.1 (odd_prime hp2)) (by have := hp.out.two_le; omega)
  have hK := two_pow_pred_mul (prime_two_le (p := p)) ha
  set N := 2 ^ (twoVal p - 1) * oddPart p
  have hsq : (g ^ N) ^ 2 = 1 := by
    rw [← pow_mul, gen_pow_eq_one_iff hg, ← hK]; exact ⟨1, by ring⟩
  have hne : g ^ N ≠ 1 := by
    rw [Ne, gen_pow_eq_one_iff hg, ← hK]
    intro h
    have hN0 : 0 < N := by have := oddPart_pos (prime_two_le (p := p)); positivity
    have h2N : 2 ^ (twoVal p - 1) * (2 * oddPart p) = 2 * N := by simp only [N]; ring
    rw [h2N] at h
    have := Nat.le_of_dvd hN0 h
    omega
  have hm1 : g ^ N = -1 := by
    rcases mul_self_eq_one_iff.1 (show g ^ N * g ^ N = 1 by rw [← sq]; exact hsq) with h | h
    · exact absurd h hne
    · exact h
  rw [← hm1, map_pow, pow_mul, hζ, (oddPart_odd prime_two_le).neg_one_pow]

lemma char_on_coset (r : ℕ) {n : ZMod p} (hn : n ∈ cosetOf (g ^ r) (Ha p)) :
    χ n = χ g ^ r := by
  have hg0 := gen_ne_zero hg
  rw [mem_cosetOf (pow_ne_zero _ hg0)] at hn
  have hdec : n = g ^ r * ((g ^ r)⁻¹ * n) := by
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hg0), one_mul]
  rw [hdec, map_mul, char_of_mem_Ha hp2 hg hζ hn, mul_one, map_pow]

/-- **The cyclotomic tower, the identity.** -/
theorem bandSumPow_eq_sum {e : ℕ} :
    bandSumPow χ e = ∑ r ∈ range (2 ^ (twoVal p - 1)),
      χ g ^ r * (pairBandSum (cosetOf (g ^ r) (Ha p)) e : R) := by
  have hg0 := gen_ne_zero hg
  set K := 2 ^ (twoVal p - 1)
  set low := univ.filter (fun n : ZMod p => 2 * n.val < p)
  set P : ℕ → ZMod p → Prop := fun r n => n ∈ cosetOf (g ^ r) (Ha p) ∨ -n ∈ cosetOf (g ^ r) (Ha p)
  have hsplit : ∀ n ∈ low, χ n * (bandSignE e n : R) =
      ∑ r ∈ range K, if P r n then χ n * (bandSignE e n : R) else 0 := by
    intro n _
    by_cases hn : n = 0
    · subst hn; simp [MulChar.map_nonunit χ not_isUnit_zero]
    · obtain ⟨r, hr, hP, huniq⟩ := exists_unique_index hp2 hg hn
      rw [sum_eq_single r (fun r' hr' hne => ite_eq_right fun h => hne (huniq r' hr' h))
        (fun h => absurd hr h), ite_eq_left hP]
  unfold bandSumPow
  rw [sum_congr rfl hsplit, sum_comm]
  refine sum_congr rfl fun r _ => ?_
  rw [← sum_filter, pairBandSum, Int.cast_sum, mul_sum]
  have hfil : low.filter (P r) =
      univ.filter (fun n : ZMod p => 2 * n.val < p ∧ (n ∈ cosetOf (g ^ r) (Ha p) ∨
        -n ∈ cosetOf (g ^ r) (Ha p))) := by
    ext n; simp [low, P]
  rw [hfil]
  refine sum_congr rfl fun n hn => ?_
  have hn' := (mem_filter.1 hn).2.2
  split_ifs with h
  · rw [char_on_coset hp2 hg hζ r h]; push_cast; ring
  · have hneg := hn'.resolve_left h
    have : χ n = -χ g ^ r := by
      rw [show n = -1 * -n by ring, map_mul, char_neg_one hp2 hg hζ,
        char_on_coset hp2 hg hζ r hneg]; ring
    rw [this]; push_cast; ring

/-- **The cyclotomic tower** (Theorem 4.3). -/
theorem cyclotomic_tower' {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    bandSumPow χ e = ∑ r ∈ range (2 ^ (twoVal p - 1)),
        χ g ^ r * (pairBandSum (cosetOf (g ^ r) (Ha p)) e : R) ∧
      ∀ r : ℕ, pairBandSum (cosetOf (g ^ r) (Ha p)) e ≡
        (oddPart p : ℤ) - 2 * oddCountZ (cosetOf (g ^ r) (Ha p)) -
          2 * oddCountZ ((cosetOf (g ^ r) (Ha p)).image (· ^ e)) [ZMOD 4] := by
  have hg0 := gen_ne_zero hg
  refine ⟨bandSumPow_eq_sum hp2 hg hζ, fun r => ?_⟩
  have hc := pow_ne_zero r hg0
  rw [pairBandSum_eq hp2 _ (zero_not_mem_coset hc) (fun x hx => neg_not_mem_coset hp2 hc hx) he he0]
  exact sum_coset_pow_modEq hc e

end Tower

end BandParityTower
