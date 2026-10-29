module

public import BandParityTower.Inversion
public import BandParityTower.Mod8Defs

@[expose] public section

/-!
# Modulo eight: the joint-parity form and the dichotomy

* `deltaForm` (Corollary 5.1): `f = 4Δ(H) + 2k + 4t - Q` and `e = 4Δ(2H) - 3k - t - Q`.
* `hminus_modEq` (Lemma 5.2): for odd `k, t` and `h = (k² + t²)/2`,
  `h ≡ 1 + 4(ε(k) + ε(t)) (mod 8)` with `ε(x) = (x² - 1)/8 mod 2`, and `h ≡ 1 (mod 8)` iff
  `k ≡ ± t (mod 8)`.
* `mod8_dichotomy` (Proposition 5.3).
-/

namespace BandParityTower

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The exact matching identity -/

omit hp in
lemma sign_prod_exact {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 - 2 * (if a = -1 then 1 else 0) - 2 * (if b = -1 then 1 else 0) +
      4 * (if a = -1 ∧ b = -1 then 1 else 0) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

omit hp in
lemma parSign_eq_neg_one_iff (x : ZMod p) : parSign x = -1 ↔ Odd x.val := by
  unfold parSign
  rcases Nat.even_or_odd x.val with h | h
  · rw [h.neg_one_pow]; simp [Nat.not_odd_iff_even.2 h]
  · rw [h.neg_one_pow]; simp [h]

/-- `∑_{x ∈ X} s(x) s(x²) = |X| - 2α(X) - 2 #{x ∈ X : ⟨x²⟩ odd} + 4Δ(X)`. -/
lemma sum_sq_exact (X : Finset (ZMod p)) :
    ∑ x ∈ X, parSign x * parSign (x ^ 2) = X.card - 2 * oddCountZ X -
      2 * (X.filter fun x => Odd (x ^ 2).val).card + 4 * jointOdd X := by
  rw [sum_congr rfl fun x _ => sign_prod_exact (parSign_eq x) (parSign_eq (x ^ 2))]
  simp only [parSign_eq_neg_one_iff, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_boole,
    sum_const, nsmul_eq_mul, mul_one]
  rfl

/-- **Corollary 5.1, the joint-parity form.** -/
theorem deltaForm' (hp8 : p % 8 = 5) (hp5 : 5 < p) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) (hpin : χ 2 = gi) :
    (bandSum χ).re = 4 * jointOdd (Ha p) + 2 * k χ + 4 * t χ - Q p ∧
      (bandSum χ).im = 4 * jointOdd (cosetOf 2 (Ha p)) - 3 * k χ - t χ - Q p := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  have hQ : oddPart p = (p - 1) / 4 := oddPart_five hp8
  have hQZ : Q p = (oddPart p : ℤ) := by rw [hQ]; rfl
  have hA := (coset_parities' hχ hp8 hp5 hpin).1
  have hB := (coset_parities' hχ hp8 hp5 hpin).2
  rw [cls_one_eq hχ hp8, sum_parSign, card_Ha] at hA
  rw [cls_gi_eq hχ hp8 hpin, sum_parSign, card_coset_Ha h20] at hB
  -- odd squares: squaring is a bijection `H → H` and `2H → 4H = -H`
  have hsqH : ((Ha p).filter fun x => Odd (x ^ 2).val).card = oddCountZ (Ha p) := by
    have hb := sq_bijOn_coset hp2 (one_ne_zero (α := ZMod p))
    simp only [cosetOf_one, one_pow] at hb
    unfold oddCountZ
    exact card_nbij (fun x => x ^ 2) (fun x hx => mem_filter.2 ⟨hb.mapsTo (mem_filter.1 hx).1,
      (mem_filter.1 hx).2⟩) (fun x hx y hy h => hb.injOn (mem_filter.1 hx).1 (mem_filter.1 hy).1 h)
      (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hb.surjOn (mem_filter.1 hy).1
        exact ⟨x, mem_filter.2 ⟨hx, (mem_filter.1 hy).2⟩, rfl⟩)
  have hm4 := neg_four_mem hp8 hχ hpin
  have h40 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h20 h20
  have hsq2H : ((cosetOf 2 (Ha p)).filter fun x => Odd (x ^ 2).val).card =
      oddPart p - oddCountZ (Ha p) := by
    have hb := sq_bijOn_coset hp2 h20
    have h4 : cosetOf ((2 : ZMod p) ^ 2) (Ha p) = (Ha p).image (fun x => -x) := by
      ext y
      rw [mem_cosetOf (pow_ne_zero 2 h20), mem_image]
      constructor
      · intro hy
        refine ⟨-y, ?_, neg_neg y⟩
        have := mul_mem_Ha hm4 hy
        convert this using 1; field_simp; ring
      · rintro ⟨x, hx, rfl⟩
        have := mul_mem_Ha (inv_mem_Ha hm4) hx
        convert this using 1; field_simp; ring
    rw [h4] at hb
    have hneg := oddCountZ_neg_image (S := Ha p) hp2 zero_not_mem_Ha
    rw [card_Ha] at hneg
    have : ((cosetOf 2 (Ha p)).filter fun x => Odd (x ^ 2).val).card =
        oddCountZ ((Ha p).image fun x => -x) := by
      unfold oddCountZ
      exact card_nbij (fun x => x ^ 2) (fun x hx => mem_filter.2 ⟨hb.mapsTo (mem_filter.1 hx).1,
        (mem_filter.1 hx).2⟩)
        (fun x hx y hy h => hb.injOn (mem_filter.1 hx).1 (mem_filter.1 hy).1 h)
        (fun y hy => by
          obtain ⟨x, hx, rfl⟩ := hb.surjOn (mem_filter.1 hy).1
          exact ⟨x, mem_filter.2 ⟨hx, (mem_filter.1 hy).2⟩, rfl⟩)
    omega
  have hf := sum_sq_exact (Ha p)
  have he := sum_sq_exact (cosetOf 2 (Ha p))
  rw [hsqH, card_Ha] at hf
  rw [hsq2H, card_coset_Ha h20] at he
  have hle : oddCountZ (Ha p) ≤ oddPart p := by
    rw [← card_Ha]; exact card_filter_le _ _
  rw [bandSum_re' hχ hp8, bandSum_im' hχ hp8, cls_one_eq hχ hp8, cls_gi_eq hχ hp8 hpin, hf, he,
    hQZ]
  push_cast [hle]
  constructor <;> linarith

/-! ### Lemma 5.2 -/

omit hp in
lemma eight_dvd_sq_sub_one {x : ℤ} (hx : Odd x) : 8 ∣ x ^ 2 - 1 := by
  obtain ⟨a, rfl⟩ := hx
  have : Even (a * (a + 1)) := Int.even_mul_succ_self a
  obtain ⟨b, hb⟩ := this
  exact ⟨b, by nlinarith [hb]⟩

omit hp in
/-- `ε(x) = (x² - 1)/8 mod 2` depends only on `x mod 8`: it is `0` for `x ≡ ± 1` and `1` for
`x ≡ ± 3`. -/
lemma eps_eq {x : ℤ} (hx : Odd x) :
    (x ^ 2 - 1) / 8 % 2 = if x % 8 = 1 ∨ x % 8 = 7 then 0 else 1 := by
  obtain ⟨a, r, hr, rfl⟩ : ∃ a r : ℤ, (r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7) ∧ x = 8 * a + r := by
    refine ⟨x / 8, x % 8, ?_, by omega⟩
    obtain ⟨b, rfl⟩ := hx; omega
  rcases hr with rfl | rfl | rfl | rfl
  · rw [show (8 * a + 1) ^ 2 - 1 = 8 * (2 * (4 * a ^ 2 + a)) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num), Int.mul_emod_right, ite_eq_left (by omega)]
  · rw [show (8 * a + 3) ^ 2 - 1 = 8 * (1 + 2 * (4 * a ^ 2 + 3 * a)) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num), Int.add_mul_emod_self_left, ite_eq_right (by omega)]
    norm_num
  · rw [show (8 * a + 5) ^ 2 - 1 = 8 * (1 + 2 * (4 * a ^ 2 + 5 * a + 1)) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num), Int.add_mul_emod_self_left, ite_eq_right (by omega)]
    norm_num
  · rw [show (8 * a + 7) ^ 2 - 1 = 8 * (2 * (4 * a ^ 2 + 7 * a + 3)) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num), Int.mul_emod_right, ite_eq_left (by omega)]

omit hp in
/-- **Lemma 5.2.** For odd `k, t` and `h = (k² + t²)/2`: `h ≡ 1 + 4(ε(k) + ε(t)) (mod 8)`, and
`h ≡ 1 (mod 8)` iff `k ≡ ± t (mod 8)`. -/
theorem hminus_modEq {k t : ℤ} (hk : Odd k) (ht : Odd t) :
    (k ^ 2 + t ^ 2) / 2 ≡ 1 + 4 * ((k ^ 2 - 1) / 8 % 2 + (t ^ 2 - 1) / 8 % 2) [ZMOD 8] ∧
      ((k ^ 2 + t ^ 2) / 2 ≡ 1 [ZMOD 8] ↔ k ≡ t [ZMOD 8] ∨ k ≡ -t [ZMOD 8]) := by
  obtain ⟨u, hu⟩ := eight_dvd_sq_sub_one hk
  obtain ⟨w, hw⟩ := eight_dvd_sq_sub_one ht
  have hh : (k ^ 2 + t ^ 2) / 2 = 1 + 4 * (u + w) := by
    rw [show k ^ 2 + t ^ 2 = 2 * (1 + 4 * (u + w)) by linarith, Int.mul_ediv_cancel_left _ two_ne_zero]
  have hu' : (k ^ 2 - 1) / 8 = u := by rw [hu, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hw' : (t ^ 2 - 1) / 8 = w := by rw [hw, Int.mul_ediv_cancel_left _ (by norm_num)]
  have ek := eps_eq hk
  have et := eps_eq ht
  rw [hu'] at ek
  rw [hw'] at et
  rw [hh, hu', hw']
  unfold Int.ModEq
  have hk2 : k % 2 = 1 := Int.odd_iff.1 hk
  have ht2 : t % 2 = 1 := Int.odd_iff.1 ht
  constructor
  · omega
  · split_ifs at ek et <;> omega

/-! ### Proposition 5.3 -/

/-- **Proposition 5.3, the mod-8 dichotomy.** With `h = (k² + t²)/2 = h⁻`: if `κ ≡ Q (mod 4)` then
`k + t ≡ h - 1 (mod 8)`; otherwise `k + t ≡ 2 (mod 4)`, and if moreover `h ≡ 1 (mod 8)` then
`k ≡ t (mod 8)`. -/
theorem mod8_dichotomy' (hp8 : p % 8 = 5) (hp5 : 5 < p) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) (hpin : χ 2 = gi) :
    (kappa p ≡ Q p [ZMOD 4] → k χ + t χ ≡ (k χ ^ 2 + t χ ^ 2) / 2 - 1 [ZMOD 8]) ∧
      (¬ kappa p ≡ Q p [ZMOD 4] → k χ + t χ ≡ 2 [ZMOD 4] ∧
        ((k χ ^ 2 + t χ ^ 2) / 2 ≡ 1 [ZMOD 8] → k χ ≡ t χ [ZMOD 8])) := by
  have hk := odd_k' hχ hp8 hp5
  have ht := odd_t' hχ hp8 hp5
  have hcc := coordinate_congruence' hχ hp8 hp5 hpin
  obtain ⟨h1, -⟩ := hminus_modEq hk ht
  obtain ⟨u, hu⟩ := eight_dvd_sq_sub_one hk
  obtain ⟨w, hw⟩ := eight_dvd_sq_sub_one ht
  have hu' : (k χ ^ 2 - 1) / 8 = u := by rw [hu, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hw' : (t χ ^ 2 - 1) / 8 = w := by rw [hw, Int.mul_ediv_cancel_left _ (by norm_num)]
  have ek := eps_eq hk
  have et := eps_eq ht
  rw [hu'] at ek h1
  rw [hw'] at et h1
  have hk2 : k χ % 2 = 1 := Int.odd_iff.1 hk
  have ht2 : t χ % 2 = 1 := Int.odd_iff.1 ht
  have hQ := odd_Q (p := p) hp8
  obtain ⟨q, hq⟩ := hQ
  unfold Int.ModEq at *
  split_ifs at ek et <;> constructor <;> intro h <;> (try constructor) <;> (try intro) <;> omega

end BandParityTower
