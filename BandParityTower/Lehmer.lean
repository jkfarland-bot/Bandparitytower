module

public import BandParityTower.Half
public import BandParityTower.Main

@[expose] public section

/-!
# E. Lehmer's criterion

E. Lehmer, *Generalizations of Gauss's lemma* (1977), Theorem 5: if `2k ∣ p - 1` and `2` is a
`k`-th power residue modulo `p`, then `2` is a `2k`-th power residue exactly when the number `ν_k`
of `k`-th power residues in `(0, p/4)` has the parity of `(p - 1)/(2k)`.

The proof is Gauss's lemma for the half-system `A` of the `k`-th power residues in `(0, p/2)`:
multiplication by `2` followed by a sign carries `A` onto itself, the sign being `-1` exactly
for the elements above `p/4`, so `2^{(p-1)/(2k)} = (-1)^{(p-1)/(2k) - ν_k}`.
-/

namespace BandParityTower

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma val_two_mul_lt (hp2 : p ≠ 2) {x : ZMod p} (hx : 2 * x.val < p) : (2 * x).val = 2 * x.val :=
  val_two_mul_of_lt hp2 hx

/-- **E. Lehmer's criterion** (Theorem 5 of *Generalizations of Gauss's lemma*). -/
theorem lehmer_criterion {k : ℕ} (hk : 2 * k ∣ p - 1) (h2 : ∃ y : ZMod p, y ^ k = 2) :
    (∃ y : ZMod p, y ^ (2 * k) = 2) ↔ powResCount k p % 2 = ((p - 1) / (2 * k)) % 2 := by
  have hp2le := prime_two_le (p := p)
  obtain ⟨n, hn⟩ := hk
  have hk0 : k ≠ 0 := by rintro rfl; omega
  have hn0 : n ≠ 0 := by rintro rfl; omega
  have h2kn : 2 ≤ 2 * k * n := by
    have := Nat.mul_le_mul (show 2 ≤ 2 * k by omega) (show 1 ≤ n by omega); simpa using this
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hpo : p % 2 = 1 := Nat.odd_iff.1 (odd_prime hp2)
  have h20 := two_ne_zero' (p := p) hp2
  have hdiv : (p - 1) / (2 * k) = n := by rw [hn]; exact Nat.mul_div_cancel_left n (by omega)
  have hkd : k ∣ p - 1 := ⟨2 * n, by rw [hn]; ring⟩
  have hdivk : (p - 1) / k = 2 * n := by
    rw [hn, show 2 * k * n = k * (2 * n) by ring]; exact Nat.mul_div_cancel_left _ (by omega)
  have crit : ∀ x : ZMod p, x ≠ 0 → ((∃ y : ZMod p, y ^ k = x) ↔ x ^ (2 * n) = 1) := by
    intro x hx; rw [exists_pow_iff hkd hx, hdivk]
  have h2n : (2 : ZMod p) ^ (2 * n) = 1 := (crit 2 h20).1 h2
  -- the half-system
  set A := univ.filter (fun x : ZMod p => 2 * x.val < p ∧ x ^ (2 * n) = 1) with hA
  have hA0 : ∀ x ∈ A, x ≠ 0 := by
    intro x hx h; rw [h] at hx
    simp only [hA, mem_filter, mem_univ, true_and, zero_pow (by omega : 2 * n ≠ 0)] at hx
    exact zero_ne_one hx.2
  -- the Gauss map
  set φ : ZMod p → ZMod p := fun x => if 4 * x.val < p then 2 * x else -(2 * x) with hφ
  have hmaps : Set.MapsTo φ (A : Set (ZMod p)) (A : Set (ZMod p)) := by
    intro x hx
    rw [mem_coe] at hx ⊢
    have hx0 := hA0 x hx
    simp only [hA, mem_filter, mem_univ, true_and] at hx ⊢
    have hv := val_two_mul_lt hp2 hx.1
    have hpow : (2 * x) ^ (2 * n) = 1 := by rw [mul_pow, h2n, hx.2, one_mul]
    simp only [hφ]
    split_ifs with h4
    · exact ⟨by rw [hv]; omega, hpow⟩
    · refine ⟨?_, by rw [(even_two_mul n).neg_pow, hpow]⟩
      rw [ZMod.neg_val, ite_eq_right (mul_ne_zero h20 hx0), hv]; omega
  have hinj : Set.InjOn φ (A : Set (ZMod p)) := by
    intro x hx y hy hxy
    rw [mem_coe] at hx hy
    have hx0 := hA0 x hx
    have hy0 := hA0 y hy
    have hxl := (mem_filter.1 hx).2.1
    have hyl := (mem_filter.1 hy).2.1
    have key : x = y ∨ x = -y := by
      simp only [hφ] at hxy
      split_ifs at hxy
      · exact Or.inl (mul_left_cancel₀ h20 hxy)
      · right; apply mul_left_cancel₀ h20; rw [hxy]; ring
      · right; apply mul_left_cancel₀ h20; rw [mul_neg, ← hxy]; ring
      · left; exact mul_left_cancel₀ h20 (neg_injective hxy)
    rcases key with h | h
    · exact h
    · exfalso
      have := (val_neg_ne hp2 hy0).1
      rw [← h] at this
      exact this hxl hyl
  have hbij : Set.BijOn φ (A : Set (ZMod p)) (A : Set (ZMod p)) :=
    BandParityTower.bijOn_of_injOn_card hmaps hinj le_rfl
  have hprod : ∏ x ∈ A, φ x = ∏ x ∈ A, x :=
    prod_nbij φ (fun x hx => hbij.mapsTo hx) (fun x hx y hy h => hbij.injOn hx hy h)
      (fun y hy => by obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy; exact ⟨x, hx, rfl⟩) (fun _ _ => rfl)
  -- `|A| = n`
  have hcardA : A.card = n := by
    have hR := card_pow_eq_one (p := p) (d := 2 * n) ⟨k, by rw [hn]; ring⟩
    have := sum_eq_two_nsmul_half hp2 (fun x : ZMod p => if x ^ (2 * n) = 1 then (1 : ℕ) else 0)
      (by simp [zero_pow (show 2 * n ≠ 0 by omega)])
      (fun x => by simp only [(even_two_mul n).neg_pow])
    rw [sum_boole, sum_boole, filter_filter, smul_eq_mul] at this
    simp only [Nat.cast_id] at this
    rw [hR] at this
    rw [hA]; omega
  -- the product
  set μ := (A.filter fun x => ¬ 4 * x.val < p).card with hμ
  have hφprod : ∏ x ∈ A, φ x = (-1) ^ μ * 2 ^ n * ∏ x ∈ A, x := by
    have : ∀ x ∈ A, φ x = (if 4 * x.val < p then 1 else -1) * 2 * x := by
      intro x _; simp only [hφ]; split_ifs <;> ring
    rw [prod_congr rfl this, prod_mul_distrib, prod_mul_distrib, prod_const, hcardA, prod_ite,
      prod_const_one, one_mul, prod_const, ← hμ]
  have hP0 : ∏ x ∈ A, x ≠ 0 := prod_ne_zero_iff.2 hA0
  have hkey : (-1 : ZMod p) ^ μ * 2 ^ n = 1 := by
    rw [hφprod] at hprod
    exact (mul_eq_right₀ hP0).1 hprod
  -- `ν = |A| - μ`
  have hν : powResCount k p = (A.filter fun x => 4 * x.val < p).card := by
    unfold powResCount
    refine card_nbij' (fun r => (r : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [mem_coe, mem_filter, mem_range] at hr
      obtain ⟨hrp, hr0, hr4, hry⟩ := hr
      have hv : ((r : ℕ) : ZMod p).val = r := ZMod.val_natCast_of_lt hrp
      have hr0' : (r : ZMod p) ≠ 0 := by
        rw [Ne, ← ZMod.val_eq_zero, hv]; omega
      simp only [hA, mem_coe, mem_filter, mem_univ, true_and, hv]
      exact ⟨⟨by omega, (crit _ hr0').1 hry⟩, hr4⟩
    · intro x hx
      simp only [hA, mem_coe, mem_filter, mem_univ, true_and] at hx
      obtain ⟨⟨hl, hx2⟩, h4⟩ := hx
      have hx0 : x ≠ 0 := by
        rintro rfl; rw [zero_pow (by omega : 2 * n ≠ 0)] at hx2; exact zero_ne_one hx2
      simp only [mem_coe, mem_filter, mem_range]
      refine ⟨ZMod.val_lt x, Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero]), h4, ?_⟩
      rw [ZMod.natCast_zmod_val]; exact (crit x hx0).2 hx2
    · intro r hr
      simp only [mem_coe, mem_filter, mem_range] at hr
      exact ZMod.val_natCast_of_lt hr.1
    · intro x _; exact ZMod.natCast_zmod_val x
  have hsplit := card_filter_add_card_filter_not (s := A) (p := fun x : ZMod p => 4 * x.val < p)
  rw [← hν, ← hμ, hcardA] at hsplit
  -- conclude
  have hneg1 : (-1 : ZMod p) ≠ 1 := neg_one_ne_one' hp2
  rw [exists_pow_iff ⟨n, hn⟩ h20, hdiv]
  constructor
  · intro h
    rw [h, mul_one] at hkey
    have hμe : Even μ := by
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      rw [hodd.neg_one_pow] at hkey
      exact hneg1 hkey
    obtain ⟨j, hj⟩ := hμe
    omega
  · intro h
    have hμe : Even μ := ⟨(n - powResCount k p) / 2, by omega⟩
    rw [hμe.neg_one_pow, one_mul] at hkey
    exact hkey

end BandParityTower
