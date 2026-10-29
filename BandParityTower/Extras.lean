module

public import BandParityTower.Defect

@[expose] public section

/-!
# Level two, the lag identity at `p ≡ 5 (mod 8)`, and squaring on `H_a`

* `im_eq_eTower`: for `p ≡ 5 (mod 8)` and `χ(2) = i`, `e = e_2` (the remark after the definition
  of `e_a` in Section 4.3).
* `two_Na_eq`: for `p ≡ 5 (mod 8)`, `2N_2 = Q + κ`, so Theorem 4.5 at `a = 2` is `e ≡ κ`
  (Corollary 4.6, first sentence).
* `lag_H`, `lag_2H`: `∑_{u ∈ H} s(u) s(2u) = -κ` and `∑_{u ∈ 2H} s(u) s(2u) = κ` (Proposition 3.5).
* `fTower_eq_cycles`: squaring permutes `H_a`, and `f_a = m - 2 r_H` with `r_H` even
  (Proposition 5.6 (1) for `O = H_a`).
-/

namespace BandParityTower

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

theorem im_eq_eTower (hp8 : p % 8 = 5) {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
    (hpin : χ 2 = gi) : (bandSum χ).im = eTower p := by
  rw [bandSum_im' hχ hp8, cls_gi_eq hχ hp8 hpin]; rfl

theorem two_Na_eq (hp8 : p % 8 = 5) : 2 * (Na p : ℤ) = Q p + kappa p := by
  have hp2 : p ≠ 2 := by omega
  have ha : twoVal p = 2 := twoVal_five hp8
  set Sq := (range p).filter (fun n => 0 < n ∧ 4 * n < p)
  have hne : ∀ n ∈ Sq, ((n : ℕ) : ZMod p) ≠ 0 := by
    intro n hn
    simp only [Sq, mem_filter, mem_range] at hn
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h; exact absurd (Nat.le_of_dvd hn.2.1 h) (by omega)
  have hNa : (Na p : ℤ) = ∑ n ∈ Sq, (if ∃ y : ZMod p, y ^ 2 = (n : ZMod p) then 1 else 0) := by
    unfold Na powResCount
    rw [ha, sum_boole]
    simp only [Nat.cast_inj, filter_filter, Sq]
    congr 1
    ext n; simp only [mem_filter, mem_range]; norm_num [and_assoc]
  have hleg : ∀ n ∈ Sq, legendreSym p (n : ℤ) =
      2 * (if ∃ y : ZMod p, y ^ 2 = (n : ZMod p) then 1 else 0) - 1 := by
    intro n hn
    have h0 := hne n hn
    have hl : legendreSym p (n : ℤ) = quadraticChar (ZMod p) (n : ZMod p) := by
      unfold legendreSym; simp
    rw [hl]
    by_cases h : ∃ y : ZMod p, y ^ 2 = (n : ZMod p)
    · rw [(quadraticChar_one_iff_isSquare h0).2 (by obtain ⟨y, hy⟩ := h; exact ⟨y, by rw [← hy]; ring⟩),
        ite_eq_left h]; norm_num
    · rw [quadraticChar_neg_one_iff_not_isSquare.2 (fun ⟨y, hy⟩ => h ⟨y, by rw [hy]; ring⟩),
        ite_eq_right h]; norm_num
  have hk : kappa p = ∑ n ∈ Sq, (2 * (if ∃ y : ZMod p, y ^ 2 = (n : ZMod p) then (1 : ℤ) else 0) - 1) :=
    sum_congr rfl hleg
  rw [hk, sum_sub_distrib, ← mul_sum, sum_const, card_first_quarter (by omega), ← hNa]
  unfold Q; simp

theorem imaginary_law_two' (hp8 : p % 8 = 5) : eTower p ≡ kappa p [ZMOD 4] := by
  have h := eTower_modEq (p := p) (by omega)
  have h2 := two_Na_eq (p := p) hp8
  have hm : (oddPart p : ℤ) = Q p := by rw [oddPart_five hp8]; rfl
  rw [hm, h2] at h
  simpa using h

theorem lag_2H (hp8 : p % 8 = 5) :
    ∑ u ∈ cosetOf 2 (Ha p), parSign u * parSign (2 * u) = kappa p := by
  rw [lag_two (by omega), two_Na_eq hp8, oddPart_five hp8]; unfold Q; ring

/-- For a coset `cH_a`, `∑_{u ∈ cH_a} s(u) s(2u)` is the sum of `s(n)` over the representatives
in `(0, p/2)` of `± cH_a`. -/
lemma lag_coset_half (hp2 : p ≠ 2) {c : ZMod p} (hc : c ≠ 0) :
    ∑ u ∈ cosetOf c (Ha p), parSign u * parSign (2 * u) =
      ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p ∧ (c⁻¹ * n) ^ (2 * oddPart p) = 1),
        parSign n := by
  have h20 := two_ne_zero' (p := p) hp2
  have hX0 := zero_not_mem_coset (p := p) hc
  have hdisj : ∀ x ∈ cosetOf c (Ha p), -x ∉ cosetOf c (Ha p) :=
    fun x hx => neg_not_mem_coset hp2 hc hx
  rw [sum_eq_sum_half_pair hp2 _ hX0 hdisj]
  refine sum_congr (by ext n; simp [pm_coset_iff hp2 hc]) fun n hn => ?_
  have hn' := (mem_filter.1 hn).2
  have hmem := (pm_coset_iff hp2 hc n).2 hn'.2
  have hn0 : n ≠ 0 := by
    rintro rfl; rcases hmem with h | h
    · exact hX0 h
    · rw [neg_zero] at h; exact hX0 h
  rw [parSign_two_mul_of_lt hp2 hn'.1]
  split_ifs
  · ring
  · rw [mul_neg, parSign_neg hp2 hn0, parSign_neg hp2 (mul_ne_zero h20 hn0),
      parSign_two_mul_of_lt hp2 hn'.1]; ring

theorem lag_H (hp8 : p % 8 = 5) :
    ∑ u ∈ Ha p, parSign u * parSign (2 * u) = -kappa p := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  set m := oddPart p
  have hm : m = (p - 1) / 4 := oddPart_five hp8
  -- `2^{2m} = -1`: `2` is a non-residue
  have h2m : (2 : ZMod p) ^ (2 * m) = -1 := by
    have hns : ¬ ∃ y : ZMod p, y ^ 2 = 2 := by
      rintro ⟨y, hy⟩
      rcases (ZMod.exists_sq_eq_two_iff hp2).1 ⟨y, by rw [← hy]; ring⟩ with h | h <;> omega
    have hcrit := exists_pow_iff (p := p) (k := 2) ⟨(p - 1) / 2, by omega⟩ h20
    rw [show (p - 1) / 2 = 2 * m by omega] at hcrit
    have hsq : ((2 : ZMod p) ^ (2 * m)) ^ 2 = 1 := by
      rw [← pow_mul, show 2 * m * 2 = p - 1 by omega]; exact pow_sub_one_eq_one h20
    rcases mul_self_eq_one_iff.1 (show (2 : ZMod p) ^ (2 * m) * 2 ^ (2 * m) = 1 by
      rw [← sq]; exact hsq) with h | h
    · exact absurd (hcrit.2 h) hns
    · exact h
  have hH := lag_coset_half hp2 (one_ne_zero (α := ZMod p))
  rw [cosetOf_one] at hH
  simp only [inv_one, one_mul] at hH
  have h2H := lag_coset_half hp2 h20
  rw [lag_2H hp8] at h2H
  -- the two filters partition the nonzero half-range
  have hzero : ∑ n ∈ univ.filter (fun n : ZMod p => 0 < n.val ∧ 2 * n.val < p), parSign n = 0 := by
    have := sum_filter_val (p := p) (fun v => 0 < v ∧ 2 * v < p) (fun v => (-1 : ℤ) ^ v)
    rw [sum_alt_half (by omega)] at this
    exact this
  have hsplit : univ.filter (fun n : ZMod p => 0 < n.val ∧ 2 * n.val < p) =
      univ.filter (fun n : ZMod p => 2 * n.val < p ∧ n ^ (2 * m) = 1) ∪
        univ.filter (fun n : ZMod p => 2 * n.val < p ∧ (2⁻¹ * n) ^ (2 * m) = 1) := by
    ext n
    simp only [mem_filter, mem_univ, true_and, mem_union]
    by_cases hn0 : n = 0
    · subst hn0; simp [zero_pow (show 2 * m ≠ 0 by omega)]
    · have hv : 0 < n.val := Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero])
      have hsq : (n ^ (2 * m)) ^ 2 = 1 := by
        rw [← pow_mul, show 2 * m * 2 = p - 1 by omega]; exact pow_sub_one_eq_one hn0
      have h2inv : (2⁻¹ * n) ^ (2 * m) = -n ^ (2 * m) := by
        rw [mul_pow, inv_pow, h2m, inv_neg, inv_one]; ring
      rw [h2inv]
      rcases mul_self_eq_one_iff.1 (show n ^ (2 * m) * n ^ (2 * m) = 1 by
        rw [← sq]; exact hsq) with h | h
      · simp [hv, h]; tauto
      · simp [hv, h]; tauto
  rw [hsplit, sum_union] at hzero
  · rw [hH]; linarith
  · rw [disjoint_left]
    intro n h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    rw [mul_pow, inv_pow, h2m, h1.2, inv_neg, inv_one] at h2
    exact neg_one_ne_one' hp2 (by simpa using h2.2)

/-- Squaring permutes `H_a`, and `f_a = m - 2 r_H` with `r_H` even. -/
theorem fTower_eq_cycles (hp2 : p ≠ 2) :
    Set.BijOn (fun x : ZMod p => x ^ 2) (Ha p : Set (ZMod p)) (Ha p : Set (ZMod p)) ∧
      fTower p = oddPart p - 2 * ((Ha p).filter fun u => parSign u ≠ parSign (u ^ 2)).card ∧
      Even ((Ha p).filter fun u => parSign u ≠ parSign (u ^ 2)).card := by
  have hb : Set.BijOn (fun x : ZMod p => x ^ 2) (Ha p : Set (ZMod p)) (Ha p : Set (ZMod p)) := by
    have := sq_bijOn_coset hp2 (one_ne_zero (α := ZMod p))
    simpa [cosetOf_one] using this
  obtain ⟨h1, h2, -⟩ := squaring_cycle' hb
  refine ⟨hb, ?_, h2⟩
  unfold fTower; rw [h1, card_Ha]

end BandParityTower
