module

public import BandParityTower.PowerMap

@[expose] public section

/-!
# The inversion map: Lehmer-type invariants (Theorem 4.11)

For `p ≡ 5 (mod 8)`, `p > 5`, the quartic character `χ` with `χ(2) = i`, `β = k + i t` and `n̄` the
inverse of `n` modulo `p`:

  `E = #{1 ≤ n ≤ (p-1)/2 : ⟨n̄⟩ even} ≡ k + t ≡ κ - Q (mod 4)`,
  `𝓛 = ∑_{n ≤ (p-1)/2} χ(n) (-1)^{n + ⟨n̄⟩} ≡ -i β̄ (mod 4)`.

The proof here is shorter than the paper's. Write `J(x) = s(2x)`, which is `+1` exactly below
`p/2`. Every sum over a half-system becomes a sum over a coset `X ∈ {H, 2H}` of a product of
signs, and a sum of `|S|` signs is `≡ |S| - 1 + (their product) (mod 4)`. The products are
evaluated through `∏_X s(x⁻¹) = ± ∏_X s(x)` (inversion carries `H` to `H` and `2H` to `-2H`) and
the coset sums `∑_H J = t - 2k`, `∑_{2H} J = -(k + 2t)`. For `E`, the map `x ↦ -(2x)⁻¹` carries
the residue half of the count onto the non-residue half, so `E` is twice a count whose parity is
a product of signs.
-/

namespace BandParityTower

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Sums and products of signs -/

omit hp in
lemma prod_sign_eq {ι : Type*} (S : Finset ι) (σ : ι → ℤ) (hσ : ∀ x ∈ S, σ x = 1 ∨ σ x = -1) :
    ∏ x ∈ S, σ x = (-1) ^ (S.filter fun x => σ x = -1).card := by
  rw [← prod_filter_mul_prod_filter_not S (fun x => σ x = -1)]
  rw [prod_congr rfl (fun x hx => (mem_filter.1 hx).2), prod_const]
  rw [prod_congr rfl (fun x hx => ((hσ x (mem_filter.1 hx).1).resolve_right
    (mem_filter.1 hx).2)), prod_const_one, mul_one]

omit hp in
lemma sum_sign_eq {ι : Type*} (S : Finset ι) (σ : ι → ℤ) (hσ : ∀ x ∈ S, σ x = 1 ∨ σ x = -1) :
    ∑ x ∈ S, σ x = S.card - 2 * (S.filter fun x => σ x = -1).card := by
  rw [← sum_filter_add_sum_filter_not S (fun x => σ x = -1)]
  rw [sum_congr rfl (fun x hx => (mem_filter.1 hx).2), sum_const]
  rw [sum_congr rfl (fun x hx => ((hσ x (mem_filter.1 hx).1).resolve_right
    (mem_filter.1 hx).2)), sum_const]
  have := card_filter_add_card_filter_not (s := S) (fun x => σ x = -1)
  simp only [nsmul_eq_mul, mul_neg, mul_one]
  have h' : ((S.filter fun x => ¬ σ x = -1).card : ℤ) =
      S.card - (S.filter fun x => σ x = -1).card := by
    have := congrArg (fun k : ℕ => (k : ℤ)) this; push_cast at this; linarith
  rw [h']; ring

omit hp in
/-- A sum of `|S|` signs is `≡ |S| - 1 + (their product) (mod 4)`. -/
lemma sum_sign_modEq_prod {ι : Type*} (S : Finset ι) (σ : ι → ℤ)
    (hσ : ∀ x ∈ S, σ x = 1 ∨ σ x = -1) :
    ∑ x ∈ S, σ x ≡ S.card - 1 + ∏ x ∈ S, σ x [ZMOD 4] := by
  rw [sum_sign_eq S σ hσ, prod_sign_eq S σ hσ]
  rcases Nat.even_or_odd (S.filter fun x => σ x = -1).card with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hj, Even.neg_one_pow ⟨j, rfl⟩]
    exact Int.modEq_iff_dvd.2 ⟨j, by push_cast; ring⟩
  · rw [hj, Odd.neg_one_pow ⟨j, rfl⟩]
    exact Int.modEq_iff_dvd.2 ⟨j, by push_cast; ring⟩

omit hp in
lemma sign_mul {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) : a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

/-! ### `J(x) = s(2x)` -/

/-- `J(x) = s(2x)`, which is `+1` for `0 < ⟨x⟩ < p/2` and `-1` for `⟨x⟩ > p/2`. -/
abbrev Jsign (x : ZMod p) : ℤ := parSign (2 * x)

lemma Jsign_neg (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) : Jsign (-x) = -Jsign x := by
  unfold Jsign; rw [mul_neg, parSign_neg hp2 (mul_ne_zero (two_ne_zero' hp2) hx)]

lemma Jsign_low (hp2 : p ≠ 2) {x : ZMod p} (hx : 2 * x.val < p) : Jsign x = 1 :=
  parSign_two_mul_of_lt hp2 hx

lemma parSign_eq_Jsign (hp2 : p ≠ 2) (y : ZMod p) : parSign y = Jsign (2⁻¹ * y) := by
  unfold Jsign; rw [← mul_assoc, mul_inv_cancel₀ (two_ne_zero' hp2), one_mul]

/-! ### The cosets `H`, `2H` and inversion -/

omit hp in
lemma re_mul_int (z : GaussianInt) (a : ℤ) : (z * a).re = z.re * a := by simp

omit hp in
lemma im_mul_int (z : GaussianInt) (a : ℤ) : (z * a).im = z.im * a := by simp

section Cosets

variable (hp8 : p % 8 = 5) {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
  (hpin : χ 2 = gi)
include hp8 hχ hpin

lemma neg_four_mem : (-4 : ZMod p) ∈ Ha p := by
  rw [← cls_one_eq hχ hp8]
  simp only [cls, mem_filter, mem_univ, true_and]
  rw [show (-4 : ZMod p) = -1 * (2 * 2) by ring, map_mul, map_mul, hpin,
    quartic_apply_neg_one χ hχ hp8]
  decide

lemma neg_inv_four_mem : -(4 : ZMod p)⁻¹ ∈ Ha p := by
  have := inv_mem_Ha (neg_four_mem hp8 hχ hpin)
  rwa [inv_neg] at this

lemma inv_mem_two_coset {x : ZMod p} (hx : x ∈ cosetOf 2 (Ha p)) :
    -x⁻¹ ∈ cosetOf 2 (Ha p) := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  rw [mem_cosetOf h20] at hx ⊢
  have := mul_mem_Ha (neg_inv_four_mem hp8 hχ hpin) (inv_mem_Ha hx)
  convert this using 1
  have hx0 : x ≠ 0 := by rintro rfl; rw [mul_zero] at hx; exact zero_not_mem_Ha hx
  have h40 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h20 h20
  field_simp
  ring

lemma neg_inv_two_mul_mem {x : ZMod p} (hx : x ∈ Ha p) : -(2 * x)⁻¹ ∈ cosetOf 2 (Ha p) := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  apply inv_mem_two_coset hp8 hχ hpin
  rw [mem_cosetOf h20, ← mul_assoc, inv_mul_cancel₀ h20, one_mul]; exact hx

/-- `∑_{x ∈ H} J(x) = t - 2k`. -/
lemma sum_J_H (hp5 : 5 < p) : ∑ x ∈ Ha p, Jsign x = t χ - 2 * k χ := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  rw [← (coset_parities' hχ hp8 hp5 hpin).2, cls_gi_eq hχ hp8 hpin, cosetOf,
    sum_image (fun x _ y _ h => mul_left_cancel₀ h20 h)]

/-- `∑_{x ∈ 2H} J(x) = -(k + 2t)`. -/
lemma sum_J_2H (hp5 : 5 < p) : ∑ x ∈ cosetOf 2 (Ha p), Jsign x = -(k χ + 2 * t χ) := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  rw [← (coset_parities' hχ hp8 hp5 hpin).1, cls_one_eq hχ hp8, cosetOf,
    sum_image (fun x _ y _ h => mul_left_cancel₀ h20 h), ← sum_neg_distrib]
  -- `2 · 2H = 4H = -H`
  have hm4 := neg_four_mem hp8 hχ hpin
  have h40 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h20 h20
  refine sum_nbij' (fun x => -(4 * x)) (fun y => -(4⁻¹ * y)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    have := mul_mem_Ha hm4 hx; rwa [neg_mul] at this
  · intro y hy
    have := mul_mem_Ha (inv_mem_Ha hm4) hy; rwa [inv_neg, neg_mul] at this
  · intro x _
    rw [mul_neg, neg_neg, ← mul_assoc, inv_mul_cancel₀ h40, one_mul]
  · intro y _
    rw [mul_neg, neg_neg, ← mul_assoc, mul_inv_cancel₀ h40, one_mul]
  · intro x hx
    have hx0 := ne_zero_of_mem_Ha hx
    show parSign (2 * (2 * x)) = -parSign (-(4 * x))
    rw [show 2 * (2 * x) = -(-(4 * x)) by ring,
      parSign_neg hp2 (neg_ne_zero.2 (mul_ne_zero h40 hx0))]

omit hp8 hχ hpin in
/-- `∏_{x ∈ H} s(x⁻¹) = ∏_{x ∈ H} s(x)`. -/
lemma prod_inv_H : ∏ x ∈ Ha p, parSign x⁻¹ = ∏ x ∈ Ha p, parSign x :=
  prod_nbij (fun x => x⁻¹) (fun x hx => inv_mem_Ha hx) (fun x _ y _ h => inv_injective h)
    (fun y hy => ⟨y⁻¹, mem_coe.2 (inv_mem_Ha (mem_coe.1 hy)), inv_inv y⟩) (fun _ _ => rfl)

/-- `∏_{x ∈ 2H} s(x⁻¹) = -∏_{x ∈ 2H} s(x)`. -/
lemma prod_inv_2H : ∏ x ∈ cosetOf 2 (Ha p), parSign x⁻¹ = -∏ x ∈ cosetOf 2 (Ha p), parSign x := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  have hQ : Odd (cosetOf 2 (Ha p)).card := by
    rw [card_coset_Ha h20]; exact oddPart_odd prime_two_le
  have h1 : ∏ x ∈ cosetOf 2 (Ha p), parSign x⁻¹ =
      ∏ x ∈ cosetOf 2 (Ha p), parSign (-(-x⁻¹)) := by simp
  rw [h1]
  have h2 : ∏ x ∈ cosetOf 2 (Ha p), parSign (-(-x⁻¹)) =
      ∏ x ∈ cosetOf 2 (Ha p), (-parSign (-x⁻¹)) := by
    refine prod_congr rfl fun x hx => ?_
    have hx0 := ne_zero_of_mem_coset h20 hx
    rw [parSign_neg hp2 (neg_ne_zero.2 (inv_ne_zero hx0))]
  rw [h2, prod_neg, hQ.neg_one_pow, neg_one_mul]
  congr 1
  exact prod_nbij (fun x => -x⁻¹) (fun x hx => inv_mem_two_coset hp8 hχ hpin hx)
    (fun x _ y _ h => inv_injective (neg_injective h))
    (fun y hy => ⟨-y⁻¹, mem_coe.2 (inv_mem_two_coset hp8 hχ hpin (mem_coe.1 hy)),
      by simp⟩) (fun _ _ => rfl)

/-- The four classes of a nonzero residue. -/
lemma classes {n : ZMod p} (hn : n ≠ 0) :
    (χ n = 1 ↔ n ∈ Ha p) ∧ (χ n = -1 ↔ -n ∈ Ha p) ∧ (χ n = gi ↔ n ∈ cosetOf 2 (Ha p)) ∧
      (χ n = -gi ↔ -n ∈ cosetOf 2 (Ha p)) := by
  have hodd := quartic_apply_neg_one χ hχ hp8
  have h1 : ∀ x : ZMod p, χ x = 1 ↔ x ∈ Ha p := fun x => by
    rw [← cls_one_eq hχ hp8]; simp [cls]
  have h2 : ∀ x : ZMod p, χ x = gi ↔ x ∈ cosetOf 2 (Ha p) := fun x => by
    rw [← cls_gi_eq hχ hp8 hpin]; simp [cls]
  refine ⟨h1 n, ?_, h2 n, ?_⟩
  · rw [← h1, char_neg hodd]; exact ⟨fun h => by rw [h, neg_neg], fun h => by
      rw [← neg_neg (χ n), h]⟩
  · rw [← h2, char_neg hodd]; exact ⟨fun h => by rw [h, neg_neg], fun h => by
      rw [← neg_neg (χ n), h]⟩

/-- The coset form of `Re 𝓛` and `Im 𝓛` over a coset `X ∈ {H, 2H}`. -/
lemma sum_half_inv (hp2 : p ≠ 2) {c : ZMod p} (hc : c ≠ 0) (f : ZMod p → ℤ)
    (hf : ∀ n, n ≠ 0 → f n = if n ∈ cosetOf c (Ha p) then 1 else if -n ∈ cosetOf c (Ha p) then -1
      else 0) (hf0 : f 0 = 0) :
    ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p), f n * (parSign n * parSign n⁻¹) =
      ∑ x ∈ cosetOf c (Ha p), Jsign x * (parSign x * parSign x⁻¹) := by
  set X := cosetOf c (Ha p)
  have hX0 := zero_not_mem_coset (p := p) hc
  have hdisj : ∀ x ∈ X, -x ∉ X := fun x hx => neg_not_mem_coset hp2 hc hx
  rw [sum_eq_sum_half_pair hp2 X hX0 hdisj]
  rw [← sum_filter_add_sum_filter_not (univ.filter fun n : ZMod p => 2 * n.val < p)
    (fun n => n ∈ X ∨ -n ∈ X), filter_filter]
  have hzero : ∑ n ∈ (univ.filter fun n : ZMod p => 2 * n.val < p).filter
      (fun n => ¬ (n ∈ X ∨ -n ∈ X)), f n * (parSign n * parSign n⁻¹) = 0 := by
    refine sum_eq_zero fun n hn => ?_
    have hn' := (mem_filter.1 hn).2
    by_cases h0 : n = 0
    · rw [h0, hf0, zero_mul]
    · rw [hf n h0]; push Not at hn'; simp [hn'.1, hn'.2]
  rw [hzero, add_zero]
  refine sum_congr rfl fun n hn => ?_
  have hn' := (mem_filter.1 hn).2
  have hn0 : n ≠ 0 := by
    rintro rfl; rcases hn'.2 with h | h
    · exact hX0 h
    · rw [neg_zero] at h; exact hX0 h
  rw [hf n hn0]
  by_cases h : n ∈ X
  · rw [ite_eq_left h, ite_eq_left h, Jsign_low hp2 hn'.1]; try ring
  · have h' := hn'.2.resolve_left h
    rw [ite_eq_right h, ite_eq_left h', ite_eq_right h, Jsign_neg hp2 hn0, Jsign_low hp2 hn'.1, inv_neg,
      parSign_neg hp2 hn0, parSign_neg hp2 (inv_ne_zero hn0)]
    ring

end Cosets

/-- **Lehmer-type invariants** (Theorem 4.11). -/
theorem lehmer_invariants' (hp8 : p % 8 = 5) (hp5 : 5 < p) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) (hpin : χ 2 = gi) :
    ((univ.filter fun n : ZMod p => n ≠ 0 ∧ 2 * n.val < p ∧ Even (n⁻¹).val).card : ℤ) ≡
        k χ + t χ [ZMOD 4] ∧
      ((univ.filter fun n : ZMod p => n ≠ 0 ∧ 2 * n.val < p ∧ Even (n⁻¹).val).card : ℤ) ≡
        kappa p - Q p [ZMOD 4] ∧
      (∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p),
        χ n * (-1) ^ (n.val + (n⁻¹).val)).re ≡ -t χ [ZMOD 4] ∧
      (∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p),
        χ n * (-1) ^ (n.val + (n⁻¹).val)).im ≡ -k χ [ZMOD 4] := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  have h40 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h20 h20
  have hQ : oddPart p = (p - 1) / 4 := oddPart_five hp8
  have hQZ : Q p = (oddPart p : ℤ) := by rw [hQ]; rfl
  set H := Ha p
  set H2 := cosetOf 2 (Ha p)
  have hcH : (H.card : ℤ) = Q p := by rw [card_Ha, hQZ]
  have hcH2 : (H2.card : ℤ) = Q p := by rw [card_coset_Ha h20, hQZ]
  have sgn : ∀ x : ZMod p, parSign x = 1 ∨ parSign x = -1 := parSign_eq
  have hpi : ∀ x : ZMod p, parSign x ^ 2 = 1 := fun x => by
    rcases sgn x with h | h <;> rw [h] <;> norm_num
  obtain ⟨qa, hqa⟩ := odd_Q (p := p) hp8
  obtain ⟨kb, hkb⟩ := odd_k' hχ hp8 hp5
  obtain ⟨tc, htc⟩ := odd_t' hχ hp8 hp5
  -- products of `J` over the cosets
  have hJH := sum_sign_modEq_prod H Jsign (fun x _ => sgn _)
  rw [sum_J_H hp8 hχ hpin hp5, hcH] at hJH
  have hJ2H := sum_sign_modEq_prod H2 Jsign (fun x _ => sgn _)
  rw [sum_J_2H hp8 hχ hpin hp5, hcH2] at hJ2H
  have hsH := sum_sign_modEq_prod H parSign (fun x _ => sgn _)
  have hcp := (coset_parities' hχ hp8 hp5 hpin).1
  rw [cls_one_eq hχ hp8] at hcp
  rw [hcp, hcH] at hsH
  -- the terms of `𝓛`
  have hterm : ∀ n : ZMod p, χ n * (-1) ^ (n.val + (n⁻¹).val) =
      χ n * (((parSign n * parSign n⁻¹ : ℤ)) : GaussianInt) := by
    intro n; unfold parSign; push_cast; rw [pow_add]
  -- the real part
  have hre : (∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p),
      χ n * (-1) ^ (n.val + (n⁻¹).val)).re =
      ∑ x ∈ H, Jsign x * (parSign x * parSign x⁻¹) := by
    rw [re_sum]
    simp only [hterm, re_mul_int]
    refine (sum_half_inv hp8 hχ hpin hp2 one_ne_zero (fun n => (χ n).re) (fun n hn => ?_)
      (by simp [MulChar.map_zero])).trans (by rw [cosetOf_one])
    rw [cosetOf_one]
    obtain ⟨c1, c2, c3, c4⟩ := classes hp8 hχ hpin hn
    rcases quartic_values χ hχ hn with h | h | h | h
    · rw [ite_eq_left (c1.1 h), h]; rfl
    · have hn1 : n ∉ H := fun h' => by rw [c1.2 h'] at h; revert h; decide
      have hn2 : -n ∉ H := fun h' => by rw [c2.2 h'] at h; revert h; decide
      rw [ite_eq_right hn1, ite_eq_right hn2, h]; rfl
    · have hn1 : n ∉ H := fun h' => by rw [c1.2 h'] at h; revert h; decide
      rw [ite_eq_right hn1, ite_eq_left (c2.1 h), h]; rfl
    · have hn1 : n ∉ H := fun h' => by rw [c1.2 h'] at h; revert h; decide
      have hn2 : -n ∉ H := fun h' => by rw [c2.2 h'] at h; revert h; decide
      rw [ite_eq_right hn1, ite_eq_right hn2, h]; rfl
  have him : (∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p),
      χ n * (-1) ^ (n.val + (n⁻¹).val)).im =
      ∑ x ∈ H2, Jsign x * (parSign x * parSign x⁻¹) := by
    rw [im_sum]
    simp only [hterm, im_mul_int]
    refine sum_half_inv hp8 hχ hpin hp2 h20 (fun n => (χ n).im) (fun n hn => ?_)
      (by simp [MulChar.map_zero])
    obtain ⟨c1, c2, c3, c4⟩ := classes hp8 hχ hpin hn
    rcases quartic_values χ hχ hn with h | h | h | h
    · have hn1 : n ∉ H2 := fun h' => by rw [c3.2 h'] at h; revert h; decide
      have hn2 : -n ∉ H2 := fun h' => by rw [c4.2 h'] at h; revert h; decide
      rw [ite_eq_right hn1, ite_eq_right hn2, h]; rfl
    · rw [ite_eq_left (c3.1 h), h]; rfl
    · have hn1 : n ∉ H2 := fun h' => by rw [c3.2 h'] at h; revert h; decide
      have hn2 : -n ∉ H2 := fun h' => by rw [c4.2 h'] at h; revert h; decide
      rw [ite_eq_right hn1, ite_eq_right hn2, h]; rfl
    · have hn1 : n ∉ H2 := fun h' => by rw [c3.2 h'] at h; revert h; decide
      rw [ite_eq_right hn1, ite_eq_left (c4.1 h), h]; rfl
  -- products over the cosets
  have hsq : ∀ S : Finset (ZMod p), (∏ x ∈ S, parSign x) ^ 2 = 1 := fun S => by
    rw [← prod_pow]; exact prod_eq_one fun x _ => hpi x
  have hprodH : ∏ x ∈ H, Jsign x * (parSign x * parSign x⁻¹) = ∏ x ∈ H, Jsign x := by
    rw [prod_mul_distrib, prod_mul_distrib, prod_inv_H, ← sq, hsq, mul_one]
  have hprod2H : ∏ x ∈ H2, Jsign x * (parSign x * parSign x⁻¹) = -∏ x ∈ H2, Jsign x := by
    rw [prod_mul_distrib, prod_mul_distrib, prod_inv_2H hp8 hχ hpin, mul_neg, ← sq, hsq]; ring
  have hGs : ∀ S : Finset (ZMod p), ∀ x ∈ S,
      Jsign x * (parSign x * parSign x⁻¹) = 1 ∨ Jsign x * (parSign x * parSign x⁻¹) = -1 :=
    fun S x _ => sign_mul (sgn _) (sign_mul (sgn _) (sgn _))
  have hLre := sum_sign_modEq_prod H _ (hGs H)
  rw [hprodH, hcH, ← hre] at hLre
  have hLim := sum_sign_modEq_prod H2 _ (hGs H2)
  rw [hprod2H, hcH2, ← him] at hLim
  -- the count `E`
  set G' : ZMod p → ℤ := fun x => Jsign x * parSign x⁻¹ with hG'
  have hG's : ∀ S : Finset (ZMod p), ∀ x ∈ S, G' x = 1 ∨ G' x = -1 :=
    fun S x _ => sign_mul (sgn _) (sgn _)
  -- the half-system sums of `s(n⁻¹)`
  have hhalf : ∀ {c : ZMod p}, c ≠ 0 →
      ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p),
        (if n ∈ cosetOf c (Ha p) ∨ -n ∈ cosetOf c (Ha p) then (1 + parSign n⁻¹) else 0) =
      Q p + ∑ x ∈ cosetOf c (Ha p), G' x := by
    intro c hc
    have hX0 := zero_not_mem_coset (p := p) hc
    have hdisj : ∀ x ∈ cosetOf c (Ha p), -x ∉ cosetOf c (Ha p) :=
      fun x hx => neg_not_mem_coset hp2 hc hx
    rw [← sum_filter]
    have h1 := sum_eq_sum_half_pair hp2 _ hX0 hdisj (fun x => 1 + G' x)
    rw [show Q p + ∑ x ∈ cosetOf c (Ha p), G' x = ∑ x ∈ cosetOf c (Ha p), (1 + G' x) by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, card_coset_Ha hc, ← hQZ], h1,
      filter_filter]
    refine sum_congr rfl fun n hn => ?_
    have hn' := (mem_filter.1 hn).2
    have hn0 : n ≠ 0 := by
      rintro rfl; rcases hn'.2 with h | h
      · exact hX0 h
      · rw [neg_zero] at h; exact hX0 h
    simp only [hG']
    split_ifs with h
    · rw [Jsign_low hp2 hn'.1, one_mul]
    · rw [Jsign_neg hp2 hn0, Jsign_low hp2 hn'.1, inv_neg, parSign_neg hp2 (inv_ne_zero hn0)]
      ring
  have hE2 : 2 * ((univ.filter fun n : ZMod p => n ≠ 0 ∧ 2 * n.val < p ∧
      Even (n⁻¹).val).card : ℤ) = 2 * Q p + ∑ x ∈ H, G' x + ∑ x ∈ H2, G' x := by
    have hcount : ((univ.filter fun n : ZMod p => n ≠ 0 ∧ 2 * n.val < p ∧
        Even (n⁻¹).val).card : ℤ) = ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p),
          (if n ≠ 0 ∧ Even (n⁻¹).val then 1 else 0) := by
      rw [sum_boole, filter_filter]
      congr 2; ext n; simp only [mem_filter, mem_univ, true_and]; tauto
    rw [hcount, mul_sum]
    have hHH := hhalf (one_ne_zero (α := ZMod p))
    have hH2 := hhalf h20
    rw [cosetOf_one] at hHH
    rw [show 2 * Q p + ∑ x ∈ H, G' x + ∑ x ∈ H2, G' x =
      (Q p + ∑ x ∈ H, G' x) + (Q p + ∑ x ∈ H2, G' x) by ring, ← hHH, ← hH2, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    by_cases hn0 : n = 0
    · subst hn0
      simp [zero_not_mem_Ha, zero_not_mem_coset h20]
    · obtain ⟨c1, c2, c3, c4⟩ := classes hp8 hχ hpin hn0
      have hev : (if n ≠ 0 ∧ Even (n⁻¹).val then (1 : ℤ) else 0) * 2 = 1 + parSign n⁻¹ := by
        unfold parSign
        rcases Nat.even_or_odd (n⁻¹).val with h | h
        · rw [ite_eq_left ⟨hn0, h⟩, h.neg_one_pow]; norm_num
        · rw [ite_eq_right (fun h' => (Nat.not_even_iff_odd.2 h) h'.2), h.neg_one_pow]; norm_num
      rw [mul_comm, hev]
      rcases quartic_values χ hχ hn0 with h | h | h | h
      · have : n ∉ H2 ∧ -n ∉ H2 := ⟨fun h' => by rw [c3.2 h'] at h; revert h; decide,
          fun h' => by rw [c4.2 h'] at h; revert h; decide⟩
        rw [ite_eq_left (Or.inl (c1.1 h)), ite_eq_right (fun h' => h'.elim this.1 this.2)]; ring
      · have : n ∉ H ∧ -n ∉ H := ⟨fun h' => by rw [c1.2 h'] at h; revert h; decide,
          fun h' => by rw [c2.2 h'] at h; revert h; decide⟩
        rw [ite_eq_right (fun h' => h'.elim this.1 this.2), ite_eq_left (Or.inl (c3.1 h))]; ring
      · have : n ∉ H2 ∧ -n ∉ H2 := ⟨fun h' => by rw [c3.2 h'] at h; revert h; decide,
          fun h' => by rw [c4.2 h'] at h; revert h; decide⟩
        rw [ite_eq_left (Or.inr (c2.1 h)), ite_eq_right (fun h' => h'.elim this.1 this.2)]; ring
      · have : n ∉ H ∧ -n ∉ H := ⟨fun h' => by rw [c1.2 h'] at h; revert h; decide,
          fun h' => by rw [c2.2 h'] at h; revert h; decide⟩
        rw [ite_eq_right (fun h' => h'.elim this.1 this.2), ite_eq_left (Or.inr (c4.1 h))]; ring
  -- `x ↦ -(2x)⁻¹` carries the residue half onto the non-residue half
  have hswap : ∑ x ∈ H2, G' x = ∑ x ∈ H, G' x := by
    symm
    refine sum_nbij' (fun x => -(2 * x)⁻¹) (fun y => -(2 * y)⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro x hx; exact neg_inv_two_mul_mem hp8 hχ hpin hx
    · intro y hy
      rw [mem_cosetOf h20] at hy
      have := mul_mem_Ha (neg_inv_four_mem hp8 hχ hpin) (inv_mem_Ha hy)
      convert this using 1
      have hy0 : y ≠ 0 := by rintro rfl; rw [mul_zero] at hy; exact zero_not_mem_Ha hy
      field_simp
      norm_num
    · intro x hx
      have hx0 := ne_zero_of_mem_Ha hx
      field_simp
    · intro y hy
      have hy0 := ne_zero_of_mem_coset h20 hy
      field_simp
    · intro x hx
      have hx0 := ne_zero_of_mem_Ha hx
      simp only [hG']
      have h2x : (2 * x)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero h20 hx0)
      rw [Jsign_neg hp2 h2x, inv_neg, inv_inv, parSign_neg hp2 (mul_ne_zero h20 hx0)]
      unfold Jsign
      rw [show 2 * (2 * x)⁻¹ = x⁻¹ by field_simp]
      ring
  rw [hswap] at hE2
  have hEsum := sum_sign_modEq_prod H G' (hG's H)
  have hprodG' : ∏ x ∈ H, G' x = (∏ x ∈ H, Jsign x) * ∏ x ∈ H, parSign x := by
    simp only [hG']; rw [prod_mul_distrib, prod_inv_H]
  rw [hprodG', hcH] at hEsum
  have hcc := coordinate_congruence' hχ hp8 hp5 hpin
  have hE : ((univ.filter fun n : ZMod p => n ≠ 0 ∧ 2 * n.val < p ∧
      Even (n⁻¹).val).card : ℤ) = Q p + ∑ x ∈ H, G' x := by linarith
  have hJ' : ∏ x ∈ H, Jsign x ≡ t χ - 2 * k χ - Q p + 1 [ZMOD 4] := by
    unfold Int.ModEq at hJH ⊢; omega
  have hs' : ∏ x ∈ H, parSign x ≡ k χ + 2 * t χ - Q p + 1 [ZMOD 4] := by
    unfold Int.ModEq at hsH ⊢; omega
  have hmul := hJ'.mul hs'
  have key : (k χ + t χ) - (2 * Q p - 1 + (t χ - 2 * k χ - Q p + 1) *
      (k χ + 2 * t χ - Q p + 1)) = 4 * (-qa ^ 2 - qa * kb + 3 * qa * tc + 2 * kb ^ 2 +
        3 * kb * tc + 4 * kb - 2 * tc ^ 2 + 1) := by
    rw [hqa, hkb, htc]; ring
  rw [hE]
  generalize hP : (∏ x ∈ H, Jsign x) * (∏ x ∈ H, parSign x) = P at hmul hEsum
  generalize hXY : (t χ - 2 * k χ - Q p + 1) * (k χ + 2 * t χ - Q p + 1) = XY at hmul key
  unfold Int.ModEq at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega

end BandParityTower
