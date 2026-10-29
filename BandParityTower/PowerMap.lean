module

public import BandParityTower.Quartic

@[expose] public section

/-!
# The power-map family (Theorem 4.1)

For `p ≡ 5 (mod 8)` and the quartic character `χ` with `χ(2) = i`, let `H = H_2` be the fourth
powers, `Q = (p - 1)/4`, `m ≥ 1`, `d = gcd(m, Q)` and `Θ_d = (-1)^{α(H) + α(H^d)}`. Then

  `Re 𝒞_{2m} ≡ Q + 1 - Θ_d`,  `Im 𝒞_{2m} ≡ (-1)^{m-1} (κ + 1 - Θ_d)  (mod 4)`.
-/

namespace BandParityTower

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
lemma twoVal_five (hp8 : p % 8 = 5) : twoVal p = 2 :=
  twoVal_eq_of (q := (p - 1) / 4) (by norm_num; omega) (by rw [Nat.odd_iff]; omega)

omit hp in
lemma oddPart_five (hp8 : p % 8 = 5) : oddPart p = (p - 1) / 4 := by
  unfold oddPart; rw [twoVal_five hp8]; norm_num

section Quartic

variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

/-- For `p ≡ 5 (mod 8)`, the kernel of `χ` is `H_a = H`. -/
lemma cls_one_eq (hp8 : p % 8 = 5) : cls χ 1 = Ha p := by
  ext x
  simp only [cls, mem_filter, mem_univ, true_and, mem_Ha_iff]
  by_cases hx : x = 0
  · subst hx
    rw [MulChar.map_zero, zero_pow (oddPart_pos prime_two_le).ne']
    simp [show (0 : GaussianInt) ≠ 1 by decide]
  · rw [char_eq_one_iff hχ hx, exists_pow_iff ⟨(p - 1) / 4, by omega⟩ hx, oddPart_five hp8]

/-- Under the pin, `C_i = 2H`. -/
lemma cls_gi_eq (hp8 : p % 8 = 5) (hpin : χ 2 = gi) : cls χ gi = cosetOf 2 (Ha p) := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  ext x
  rw [mem_cosetOf h20, ← cls_one_eq hχ hp8]
  simp only [cls, mem_filter, mem_univ, true_and]
  have hx : χ x = gi * χ (2⁻¹ * x) := by
    rw [← hpin, ← map_mul, ← mul_assoc, mul_inv_cancel₀ h20, one_mul]
  constructor
  · intro h; rw [hx] at h; exact mul_left_cancel₀ gi_ne_zero (h.trans (mul_one gi).symm)
  · intro h; rw [hx, h, mul_one]

/-- **Coset form of `𝒞_e`** for even `e ≥ 2`. -/
theorem bandSumPow_eq (hp8 : p % 8 = 5) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    bandSumPow χ e = ((∑ u ∈ cls χ 1, parSign u * parSign (u ^ e) : ℤ) : GaussianInt)
      + gi * ((∑ u ∈ cls χ gi, parSign u * parSign (u ^ e) : ℤ) : GaussianInt) := by
  have hp2 : p ≠ 2 := by omega
  have hodd := quartic_apply_neg_one χ hχ hp8
  set w : ZMod p → ℤ := fun x => parSign x * parSign (x ^ e) with hw
  have hwodd : ∀ x ≠ 0, w (-x) = -w x := by
    intro x hx; simp only [hw, he.neg_pow, parSign_neg hp2 hx, neg_mul]
  have hfull := sum_char_mul_odd hχ hodd w hwodd
  have hhalf := sum_eq_two_nsmul_half hp2 (fun x => χ x * (w x : GaussianInt))
    (by simp [MulChar.map_zero]) (fun x => by
      by_cases hx : x = 0
      · subst hx; simp
      · simp only [hwodd x hx, char_neg hodd]; push_cast; ring)
  have hB : bandSumPow χ e = ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p),
      χ x * (w x : GaussianInt) := by
    unfold bandSumPow
    refine sum_congr rfl fun x _ => ?_
    rw [hw]; simp only
    rw [← bandSignE_eq hp2 he0 x]
  rw [← hB, two_nsmul, ← two_mul, hfull] at hhalf
  exact (mul_left_cancel₀ two_ne_zero hhalf).symm

end Quartic

/-! ### Images of `H` under power maps -/

lemma image_pow_eq_of_gcd {e₁ e₂ : ℕ} (h : Nat.gcd e₁ (oddPart p) = Nat.gcd e₂ (oddPart p)) :
    (Ha p).image (· ^ e₁) = (Ha p).image (· ^ e₂) := by
  -- both are the image under `x ↦ x^{gcd(e, m)}`
  have key : ∀ e : ℕ, (Ha p).image (· ^ e) = (Ha p).image (· ^ Nat.gcd e (oddPart p)) := by
    intro e
    ext y
    simp only [mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, ht⟩ := Nat.gcd_dvd_left e (oddPart p)
      exact ⟨x ^ t, pow_mem_Ha hx t, by rw [← pow_mul, mul_comm, ← ht]⟩
    · rintro ⟨x, hx, rfl⟩
      have hx1 : x ^ oddPart p = 1 := (mem_Ha_iff x).1 hx
      by_cases hlt : Nat.gcd e (oddPart p) < oddPart p
      · obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_gcd hlt
        refine ⟨x ^ u, pow_mem_Ha hx u, ?_⟩
        rw [← pow_mul, ← hu, mul_comm u e]
        conv_lhs => rw [← Nat.mod_add_div (e * u) (oddPart p), pow_add, pow_mul, hx1, one_pow,
          mul_one]
      · have hd : Nat.gcd e (oddPart p) = oddPart p :=
          le_antisymm (Nat.gcd_le_right _ (oddPart_pos prime_two_le)) (by omega)
        refine ⟨1, by rw [mem_Ha_iff, one_pow], ?_⟩
        rw [one_pow, hd, hx1]
  rw [key e₁, key e₂, h]

lemma oddCountZ_neg_image {S : Finset (ZMod p)} (hp2 : p ≠ 2) (hS : (0 : ZMod p) ∉ S) :
    oddCountZ (S.image (fun x => -x)) + oddCountZ S = S.card := by
  unfold oddCountZ
  have hpo : p % 2 = 1 := Nat.odd_iff.1 (odd_prime hp2)
  rw [filter_image, card_image_of_injective _ neg_injective]
  have : (S.filter fun x => Odd (-x).val) = S.filter fun x => ¬ Odd x.val := by
    refine filter_congr fun x hx => ?_
    have hx0 : x ≠ 0 := by rintro rfl; exact hS hx
    rw [ZMod.neg_val, ite_eq_right hx0]
    have := ZMod.val_lt x
    rw [Nat.odd_sub (by omega), Nat.odd_iff, Nat.odd_iff]
    simp only [hpo, true_iff, Nat.even_iff]
    omega
  rw [this, add_comm]
  exact card_filter_add_card_filter_not _

lemma card_image_pow_odd (e : ℕ) : Odd ((Ha p).image (· ^ e)).card := by
  have h := card_filter_pow_Ha (p := p) (c := 1) one_ne_zero e (fun _ => True)
  simp only [filter_true, cosetOf_one] at h
  rw [card_Ha] at h
  exact Odd.of_dvd_nat (oddPart_odd prime_two_le) ⟨_, by rw [mul_comm]; exact h⟩

lemma mul_mem_image_pow {d : ℕ} {x y : ZMod p} (hx : x ∈ (Ha p).image (· ^ d))
    (hy : y ∈ (Ha p).image (· ^ d)) : x * y ∈ (Ha p).image (· ^ d) := by
  obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hy
  exact mem_image.2 ⟨a * b, mul_mem_Ha ha hb, by simp only [mul_pow]⟩

lemma cosetOf_image_pow {d : ℕ} {c : ZMod p} (hc : c ∈ (Ha p).image (· ^ d)) :
    cosetOf c ((Ha p).image (· ^ d)) = (Ha p).image (· ^ d) := by
  have hc0 : c ≠ 0 := by
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hc; exact pow_ne_zero _ (ne_zero_of_mem_Ha ha)
  refine eq_of_subset_of_card_le (fun y hy => ?_) (by rw [card_cosetOf hc0])
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
  exact mul_mem_image_pow hc hx

lemma cosetOf_cosetOf (a b : ZMod p) (S : Finset (ZMod p)) :
    cosetOf a (cosetOf b S) = cosetOf (a * b) S := by
  simp only [cosetOf, image_image]; congr 1; ext x; simp [mul_assoc]

/-- `(2H)^{2m} = (-1)^m H^{gcd(m, Q)}` for `p ≡ 5 (mod 8)`. -/
lemma image_two_coset (hp8 : p % 8 = 5) {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
    (hpin : χ 2 = gi) (m : ℕ) :
    (cosetOf 2 (Ha p)).image (· ^ (2 * m)) =
      cosetOf ((-1) ^ m) ((Ha p).image (· ^ Nat.gcd m ((p - 1) / 4))) := by
  have hQ : oddPart p = (p - 1) / 4 := oddPart_five hp8
  have hQodd : Odd ((p - 1) / 4) := by rw [Nat.odd_iff]; omega
  set d := Nat.gcd m ((p - 1) / 4)
  have hgm : (Ha p).image (· ^ m) = (Ha p).image (· ^ d) :=
    image_pow_eq_of_gcd (by rw [hQ]; simp only [d]; rw [Nat.gcd_assoc, Nat.gcd_self])
  have hg2m : (Ha p).image (· ^ (2 * m)) = (Ha p).image (· ^ d) := by
    refine image_pow_eq_of_gcd ?_
    rw [hQ, Nat.Coprime.gcd_mul_left_cancel m (Nat.coprime_two_left.2 hQodd)]
    simp only [d]; rw [Nat.gcd_assoc, Nat.gcd_self]
  have hm4 : (-4 : ZMod p) ∈ Ha p := by
    rw [← cls_one_eq hχ hp8]
    simp only [cls, mem_filter, mem_univ, true_and]
    rw [show (-4 : ZMod p) = -1 * (2 * 2) by ring, map_mul, map_mul, hpin,
      quartic_apply_neg_one χ hχ hp8]
    decide
  have hm4d : (-4 : ZMod p) ^ m ∈ (Ha p).image (· ^ d) := by
    rw [← hgm]; exact mem_image_of_mem _ hm4
  have hY : (cosetOf 2 (Ha p)).image (· ^ (2 * m)) =
      cosetOf ((2 : ZMod p) ^ (2 * m)) ((Ha p).image (· ^ (2 * m))) := by
    simp only [cosetOf, image_image]
    congr 1; ext x; simp [mul_pow]
  rw [hY, hg2m, show (2 : ZMod p) ^ (2 * m) = (-1) ^ m * (-4) ^ m by
    rw [← mul_pow, pow_mul]; norm_num, ← cosetOf_cosetOf, cosetOf_image_pow hm4d]

/-- **The power-map family** (Theorem 4.1). -/
theorem power_map_family' (hp8 : p % 8 = 5) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) (hpin : χ 2 = gi) {m : ℕ} (hm : 1 ≤ m) :
    (bandSumPow χ (2 * m)).re ≡ Q p + 1 - (-1) ^ (oddCountZ (Ha p) +
        oddCountZ ((Ha p).image (· ^ Nat.gcd m ((p - 1) / 4)))) [ZMOD 4] ∧
      (bandSumPow χ (2 * m)).im ≡ (-1) ^ (m - 1) * (kappa p + 1 - (-1) ^ (oddCountZ (Ha p) +
        oddCountZ ((Ha p).image (· ^ Nat.gcd m ((p - 1) / 4))))) [ZMOD 4] := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  have hQ : oddPart p = (p - 1) / 4 := oddPart_five hp8
  have hQodd : Odd ((p - 1) / 4) := by rw [Nat.odd_iff]; omega
  have hQZ : Q p = (oddPart p : ℤ) := by rw [hQ]; rfl
  set d := Nat.gcd m ((p - 1) / 4)
  set Sd := (Ha p).image (· ^ d)
  set α₁ := oddCountZ (Ha p)
  set α₂ := oddCountZ Sd
  set β := oddCountZ (cosetOf 2 (Ha p))
  have hS0 : (0 : ZMod p) ∉ Sd := by
    intro h; obtain ⟨x, hx, hx0⟩ := mem_image.1 h
    exact pow_ne_zero _ (ne_zero_of_mem_Ha hx) hx0
  -- the coset forms
  have hcoset : ∀ e : ℕ, Even e → e ≠ 0 →
      (bandSumPow χ e).re = ∑ u ∈ Ha p, parSign u * parSign (u ^ e) ∧
      (bandSumPow χ e).im = ∑ u ∈ cosetOf 2 (Ha p), parSign u * parSign (u ^ e) := by
    intro e he he0
    have hB := bandSumPow_eq hχ hp8 he he0
    rw [cls_one_eq hχ hp8, cls_gi_eq hχ hp8 hpin] at hB
    exact ⟨by rw [hB, re_add_gi_mul], by rw [hB, im_add_gi_mul]⟩
  -- real part
  have hR := sum_coset_pow_modEq (p := p) (c := 1) one_ne_zero (2 * m)
  rw [cosetOf_one, image_pow_eq_of_gcd (e₂ := d) (by
    rw [hQ, Nat.Coprime.gcd_mul_left_cancel m (Nat.coprime_two_left.2 hQodd)]
    simp only [d]; rw [Nat.gcd_assoc, Nat.gcd_self])] at hR
  -- Theorem A at `m = 1`, through the coset form
  have hA := bandSum_im_modEq' hχ hp8 hpin
  have hb2 : (bandSum χ).im = (bandSumPow χ 2).im := by
    unfold bandSum bandSumPow bandSignE band; push_cast; rfl
  rw [hb2, (hcoset 2 even_two two_ne_zero).2] at hA
  have hI1 := sum_coset_pow_modEq (p := p) h20 2
  rw [show (2 : ℕ) = 2 * 1 by rfl, image_two_coset hp8 hχ hpin 1] at hI1
  simp only [Nat.gcd_one_left, pow_one, image_id'] at hI1
  have hneg1 : oddCountZ (cosetOf (-1) (Ha p)) + α₁ = oddPart p := by
    have := oddCountZ_neg_image (S := Ha p) hp2 zero_not_mem_Ha
    rw [card_Ha] at this
    rw [← this]; congr 2; simp [cosetOf]
  have hκ := hA.symm.trans hI1
  -- imaginary part
  have hI := sum_coset_pow_modEq (p := p) h20 (2 * m)
  rw [image_two_coset hp8 hχ hpin m] at hI
  change _ ≡ _ - 2 * (oddCountZ (cosetOf ((-1) ^ m) Sd) : ℤ) [ZMOD 4] at hI
  obtain ⟨c, hc⟩ := card_image_pow_odd (p := p) d
  rw [(hcoset (2 * m) (even_two_mul m) (by omega)).1]
  rw [(hcoset (2 * m) (even_two_mul m) (by omega)).2]
  obtain ⟨q, hq⟩ := hQodd
  have hQq : (oddPart p : ℤ) = 2 * q + 1 := by rw [hQ, hq]; push_cast; ring
  rw [hQZ]
  rw [hQq] at hR hI hκ ⊢
  change _ ≡ _ - 2 * (α₁ : ℤ) - 2 * (α₂ : ℤ) [ZMOD 4] at hR
  constructor
  · refine hR.trans ?_
    rcases Nat.even_or_odd (α₁ + α₂) with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [hj, Even.neg_one_pow ⟨j, rfl⟩]
      have : (α₁ : ℤ) + α₂ = j + j := by exact_mod_cast hj
      exact Int.modEq_iff_dvd.2 ⟨j, by linarith⟩
    · rw [hj, Odd.neg_one_pow ⟨j, rfl⟩]
      have : (α₁ : ℤ) + α₂ = 2 * j + 1 := by exact_mod_cast hj
      exact Int.modEq_iff_dvd.2 ⟨j + 1, by linarith⟩
  · refine hI.trans ?_
    have hneg1' : (oddCountZ (cosetOf (-1) (Ha p)) : ℤ) = 2 * q + 1 - α₁ := by
      have := congrArg (fun k : ℕ => (k : ℤ)) hneg1; push_cast at this; linarith
    rw [hneg1'] at hκ
    unfold Int.ModEq at hκ ⊢
    rcases Nat.even_or_odd m with ⟨l, hl⟩ | ⟨l, hl⟩
    · -- `m` even: `Y = H^d`
      have hpm : (-1 : ZMod p) ^ m = 1 := by rw [hl, ← two_mul, pow_mul]; norm_num
      have hs : (-1 : ℤ) ^ (m - 1) = -1 := by
        rw [show m - 1 = 2 * (l - 1) + 1 by omega, pow_succ, pow_mul]; norm_num
      rw [hpm, cosetOf_one, hs]
      rcases Nat.even_or_odd (α₁ + α₂) with ⟨j, hj⟩ | ⟨j, hj⟩
      · rw [hj, Even.neg_one_pow ⟨j, rfl⟩]
        have : (α₁ : ℤ) + α₂ = j + j := by exact_mod_cast hj
        omega
      · rw [hj, Odd.neg_one_pow ⟨j, rfl⟩]
        have : (α₁ : ℤ) + α₂ = 2 * j + 1 := by exact_mod_cast hj
        omega
    · -- `m` odd: `Y = -H^d`
      have hpm : (-1 : ZMod p) ^ m = -1 := by rw [hl, pow_succ, pow_mul]; norm_num
      have hs : (-1 : ℤ) ^ (m - 1) = 1 := by
        rw [show m - 1 = 2 * l by omega, pow_mul]; norm_num
      have hY : cosetOf (-1 : ZMod p) Sd = Sd.image (fun x => -x) := by
        simp only [cosetOf, neg_one_mul]
      have hn := oddCountZ_neg_image hp2 hS0
      rw [hc] at hn
      have hn' : (oddCountZ (Sd.image (fun x => -x)) : ℤ) = 2 * c + 1 - α₂ := by
        have := congrArg (fun k : ℕ => (k : ℤ)) hn; push_cast at this; linarith
      rw [hpm, hY, hn', hs, one_mul]
      rcases Nat.even_or_odd (α₁ + α₂) with ⟨j, hj⟩ | ⟨j, hj⟩
      · rw [hj, Even.neg_one_pow ⟨j, rfl⟩]
        have : (α₁ : ℤ) + α₂ = j + j := by exact_mod_cast hj
        omega
      · rw [hj, Odd.neg_one_pow ⟨j, rfl⟩]
        have : (α₁ : ℤ) + α₂ = 2 * j + 1 := by exact_mod_cast hj
        omega

end BandParityTower
