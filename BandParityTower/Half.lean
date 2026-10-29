module

public import BandParityTower.Group
public import BandParityTower.Matching

@[expose] public section

/-!
# Pairs of cosets over the half range

* `sum_eq_sum_half_pair`: for a set `X` with `X ∩ (-X) = ∅` and `0 ∉ X`, a sum over `X` is a sum
  over the representatives in `(0, p/2)` of `X ∪ (-X)`.
* `bandSignE_eq`: the parity dictionary `(-1)^{⌊⟨x⟩^e/p⌋} = s(x) s(x^e)`.
* `pairBandSum_eq`: the representative identity `T = ∑_{u ∈ X} s(u) s(u^e)` for even `e`.
* `sum_coset_pow_modEq`: for a coset `X = cH_a`, `∑_{u ∈ X} s(u) s(u^e) ≡ m - 2α(X) - 2α(X^e)
  (mod 4)`; with the representative identity this is the odd-subgroup congruence for `H_a`.
-/

namespace BandParityTower

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma odd_prime (hp2 : p ≠ 2) : Odd p := hp.out.odd_of_ne_two hp2

lemma mem_cosetOf {c : ZMod p} (hc : c ≠ 0) {S : Finset (ZMod p)} {x : ZMod p} :
    x ∈ cosetOf c S ↔ c⁻¹ * x ∈ S := by
  simp only [cosetOf, mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  · intro h; exact ⟨_, h, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩

lemma card_cosetOf {c : ZMod p} (hc : c ≠ 0) (S : Finset (ZMod p)) :
    (cosetOf c S).card = S.card :=
  card_image_of_injective _ (mul_right_injective₀ hc)

lemma val_neg_ne (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) :
    (2 * (-x).val < p ↔ ¬ 2 * x.val < p) := by
  rw [ZMod.neg_val, ite_eq_right hx]
  have hv := ZMod.val_lt x
  have hpo : p % 2 = 1 := Nat.odd_iff.1 (odd_prime hp2)
  omega

/-- **Reduction to the half range.** If `0 ∉ X` and `X ∩ (-X) = ∅`, then
`∑_{x ∈ X} F x = ∑_{n} (F n or F (-n))` over the representatives `n ∈ (0, p/2)` of `X ∪ (-X)`. -/
lemma sum_eq_sum_half_pair {R : Type*} [AddCommMonoid R] (hp2 : p ≠ 2) (X : Finset (ZMod p))
    (hX0 : (0 : ZMod p) ∉ X) (hdisj : ∀ x ∈ X, -x ∉ X) (F : ZMod p → R) :
    ∑ x ∈ X, F x = ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p ∧ (n ∈ X ∨ -n ∈ X)),
      (if n ∈ X then F n else F (-n)) := by
  rw [← Finset.sum_filter_add_sum_filter_not X (fun x : ZMod p => 2 * x.val < p)]
  have hsplit : univ.filter (fun n : ZMod p => 2 * n.val < p ∧ (n ∈ X ∨ -n ∈ X)) =
      X.filter (fun x => 2 * x.val < p) ∪
        (X.filter (fun x => ¬ 2 * x.val < p)).image (fun x => -x) := by
    ext n
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_image]
    constructor
    · rintro ⟨hl, hn | hn⟩
      · exact Or.inl ⟨hn, hl⟩
      · refine Or.inr ⟨-n, ⟨hn, ?_⟩, neg_neg n⟩
        have hn0 : n ≠ 0 := by rintro rfl; rw [neg_zero] at hn; exact hX0 hn
        exact (val_neg_ne hp2 (neg_ne_zero.2 hn0)).1 (by rwa [neg_neg])
    · rintro (⟨hn, hl⟩ | ⟨x, ⟨hx, hl⟩, rfl⟩)
      · exact ⟨hl, Or.inl hn⟩
      · have hx0 : x ≠ 0 := by rintro rfl; exact hX0 hx
        exact ⟨(val_neg_ne hp2 hx0).2 hl, Or.inr (by rwa [neg_neg])⟩
  rw [hsplit, sum_union, sum_image (fun x _ y _ h => neg_injective h)]
  · congr 1
    · exact sum_congr rfl fun x hx => by rw [ite_eq_left (mem_filter.1 hx).1]
    · refine sum_congr rfl fun x hx => ?_
      have hx' := (mem_filter.1 hx).1
      rw [ite_eq_right (hdisj x hx'), neg_neg]
  · rw [disjoint_left]
    rintro n hn hn'
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hn'
    exact hdisj x (mem_filter.1 hx).1 (mem_filter.1 hn).1

/-- **Parity dictionary.** `(-1)^{⌊⟨x⟩^e/p⌋} = s(x) s(x^e)` for `e ≥ 1`. -/
lemma bandSignE_eq (hp2 : p ≠ 2) {e : ℕ} (he0 : e ≠ 0) (x : ZMod p) :
    bandSignE e x = parSign x * parSign (x ^ e) := by
  unfold bandSignE parSign
  set v := x.val with hv
  have hval : (x ^ e).val = v ^ e % p := by
    rw [show x = ((v : ℕ) : ZMod p) by rw [hv, ZMod.natCast_zmod_val], ← Nat.cast_pow,
      ZMod.val_natCast]
  rw [hval]
  have hpo := odd_prime hp2
  have h1 : (-1 : ℤ) ^ (v ^ e) = (-1) ^ v := by
    rcases Nat.even_or_odd v with h | h
    · rw [h.neg_one_pow, (Nat.even_pow.2 ⟨h, he0⟩).neg_one_pow]
    · rw [h.neg_one_pow, (h.pow).neg_one_pow]
  have h2 : (-1 : ℤ) ^ (v ^ e) = (-1) ^ (v ^ e / p) * (-1) ^ (v ^ e % p) := by
    conv_lhs => rw [← Nat.div_add_mod (v ^ e) p]
    rw [pow_add, pow_mul, hpo.neg_one_pow]
  have hr : (-1 : ℤ) ^ (v ^ e % p) * (-1) ^ (v ^ e % p) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have E := h1.symm.trans h2
  linear_combination (-((-1 : ℤ) ^ (v ^ e % p))) * E + (-((-1 : ℤ) ^ (v ^ e / p))) * hr

/-- **Representative identity.** For even `e ≥ 2`, `0 ∉ X` and `X ∩ (-X) = ∅`,
`pairBandSum X e = ∑_{u ∈ X} s(u) s(u^e)`. -/
theorem pairBandSum_eq (hp2 : p ≠ 2) (X : Finset (ZMod p)) (hX0 : (0 : ZMod p) ∉ X)
    (hdisj : ∀ x ∈ X, -x ∉ X) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    pairBandSum X e = ∑ x ∈ X, parSign x * parSign (x ^ e) := by
  rw [sum_eq_sum_half_pair hp2 X hX0 hdisj, pairBandSum]
  refine sum_congr rfl fun n hn => ?_
  rw [bandSignE_eq hp2 he0]
  split_ifs with h
  · ring
  · have hn0 : n ≠ 0 := by
      rintro rfl
      simp only [mem_filter, mem_univ, true_and, neg_zero] at hn
      rcases hn.2 with h' | h' <;> exact hX0 h'
    rw [parSign_neg hp2 hn0, he.neg_pow]; ring

/-! ### `H_a` and its cosets -/

lemma neg_one_pow_oddPart (_hp2 : p ≠ 2) : (-1 : ZMod p) ^ oddPart p = -1 :=
  (oddPart_odd prime_two_le).neg_one_pow

lemma neg_one_ne_one' (hp2 : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  have : Fact (2 < p) := ⟨by have := hp.out.two_le; omega⟩
  exact ZMod.neg_one_ne_one

lemma zero_not_mem_Ha : (0 : ZMod p) ∉ Ha p := by
  rw [mem_Ha_iff, zero_pow (oddPart_pos prime_two_le).ne']; exact zero_ne_one

lemma ne_zero_of_mem_Ha {x : ZMod p} (hx : x ∈ Ha p) : x ≠ 0 := by
  rintro rfl; exact zero_not_mem_Ha hx

lemma mul_mem_Ha {x y : ZMod p} (hx : x ∈ Ha p) (hy : y ∈ Ha p) : x * y ∈ Ha p := by
  rw [mem_Ha_iff] at *; rw [mul_pow, hx, hy, one_mul]

lemma inv_mem_Ha {x : ZMod p} (hx : x ∈ Ha p) : x⁻¹ ∈ Ha p := by
  rw [mem_Ha_iff] at *; rw [inv_pow, hx, inv_one]

lemma pow_mem_Ha {x : ZMod p} (hx : x ∈ Ha p) (j : ℕ) : x ^ j ∈ Ha p := by
  rw [mem_Ha_iff] at *; rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]

lemma neg_one_not_mem_Ha (hp2 : p ≠ 2) : (-1 : ZMod p) ∉ Ha p := by
  rw [mem_Ha_iff, neg_one_pow_oddPart hp2]; exact neg_one_ne_one' hp2

lemma mem_coset_iff {c : ZMod p} (hc : c ≠ 0) {x : ZMod p} :
    x ∈ cosetOf c (Ha p) ↔ (c⁻¹ * x) ^ oddPart p = 1 := by
  rw [mem_cosetOf hc, mem_Ha_iff]

lemma zero_not_mem_coset {c : ZMod p} (hc : c ≠ 0) : (0 : ZMod p) ∉ cosetOf c (Ha p) := by
  rw [mem_cosetOf hc, mul_zero]; exact zero_not_mem_Ha

lemma ne_zero_of_mem_coset {c : ZMod p} (hc : c ≠ 0) {x : ZMod p} (hx : x ∈ cosetOf c (Ha p)) :
    x ≠ 0 := by rintro rfl; exact zero_not_mem_coset hc hx

lemma neg_not_mem_coset (hp2 : p ≠ 2) {c : ZMod p} (hc : c ≠ 0) {x : ZMod p}
    (hx : x ∈ cosetOf c (Ha p)) : -x ∉ cosetOf c (Ha p) := by
  rw [mem_cosetOf hc] at *
  intro h
  have hx0 : c⁻¹ * x ≠ 0 := ne_zero_of_mem_Ha hx
  have := mul_mem_Ha h (inv_mem_Ha hx)
  rw [mul_neg, neg_mul, mul_inv_cancel₀ hx0] at this
  exact neg_one_not_mem_Ha hp2 this

lemma card_coset_Ha {c : ZMod p} (hc : c ≠ 0) : (cosetOf c (Ha p)).card = oddPart p := by
  rw [card_cosetOf hc, card_Ha]

/-- Fibres of `u ↦ u^e` on a coset of `H_a` have `gcd(m, e)` elements. -/
lemma card_fibre_Ha {c : ZMod p} (hc : c ≠ 0) (e : ℕ) {u₀ : ZMod p}
    (hu₀ : u₀ ∈ cosetOf c (Ha p)) :
    ((cosetOf c (Ha p)).filter (fun u => u ^ e = u₀ ^ e)).card = Nat.gcd (oddPart p) e := by
  have hu0 : u₀ ≠ 0 := ne_zero_of_mem_coset hc hu₀
  have hd : Nat.gcd (oddPart p) e ∣ p - 1 :=
    (Nat.gcd_dvd_left _ _).trans ⟨2 ^ twoVal p, by rw [mul_comm, two_pow_mul_oddPart prime_two_le]⟩
  rw [← card_pow_eq_one hd]
  refine card_nbij' (fun u => u₀⁻¹ * u) (fun k => u₀ * k) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hu ⊢
    rw [mem_cosetOf hc] at hu hu₀
    have h1 : (u₀⁻¹ * u) ^ oddPart p = 1 := by
      have := mul_mem_Ha (inv_mem_Ha hu₀) hu.1
      rw [mem_Ha_iff] at this
      rwa [mul_inv_rev, inv_inv, mul_assoc, ← mul_assoc c, mul_inv_cancel₀ hc, one_mul] at this
    have h2 : (u₀⁻¹ * u) ^ e = 1 := by
      rw [mul_pow, inv_pow, hu.2, inv_mul_cancel₀ (pow_ne_zero _ hu0)]
    exact pow_gcd_eq_one.2 ⟨h1, h2⟩
  · intro k hk
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hk ⊢
    have h1 : k ^ oddPart p = 1 := by
      obtain ⟨q, hq⟩ := Nat.gcd_dvd_left (oddPart p) e
      rw [hq, pow_mul, hk, one_pow]
    have h2 : k ^ e = 1 := by
      obtain ⟨q, hq⟩ := Nat.gcd_dvd_right (oddPart p) e
      rw [hq, pow_mul, hk, one_pow]
    refine ⟨?_, by rw [mul_pow, h2, mul_one]⟩
    rw [mem_cosetOf hc] at hu₀ ⊢
    rw [← mul_assoc]; exact mul_mem_Ha hu₀ (by rw [mem_Ha_iff]; exact h1)
  · intro u _; simp only; rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]
  · intro k _; simp only; rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]

lemma card_filter_pow_Ha {c : ZMod p} (hc : c ≠ 0) (e : ℕ) (P : ZMod p → Prop) [DecidablePred P] :
    ((cosetOf c (Ha p)).filter (fun u => P (u ^ e))).card =
      Nat.gcd (oddPart p) e * (((cosetOf c (Ha p)).image (· ^ e)).filter P).card := by
  rw [card_eq_sum_card_fiberwise (f := (· ^ e))
    (t := ((cosetOf c (Ha p)).image (· ^ e)).filter P)
    (fun u hu => by
      simp only [mem_coe, mem_filter] at hu ⊢
      exact ⟨mem_image_of_mem _ hu.1, hu.2⟩)]
  rw [sum_congr rfl (g := fun _ => Nat.gcd (oddPart p) e), sum_const, smul_eq_mul, mul_comm]
  intro y hy
  simp only [mem_filter, mem_image] at hy
  obtain ⟨⟨u₀, hu₀, rfl⟩, hP⟩ := hy
  rw [← card_fibre_Ha hc e hu₀, filter_filter]
  congr 1; ext u
  simp only [mem_filter]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨h1, by rw [h3]; exact hP, h3⟩

omit hp in
lemma sum_parSign [NeZero p] (S : Finset (ZMod p)) :
    ∑ u ∈ S, parSign u = (S.card : ℤ) - 2 * oddCountZ S := by
  unfold oddCountZ
  have : ∀ u : ZMod p, parSign u = 1 - 2 * (if Odd u.val then 1 else 0) := by
    intro u; unfold parSign
    rcases Nat.even_or_odd u.val with h | h
    · rw [h.neg_one_pow, ite_eq_right (Nat.not_odd_iff_even.2 h)]; ring
    · rw [h.neg_one_pow, ite_eq_left h]; ring
  rw [sum_congr rfl (fun u _ => this u), sum_sub_distrib, ← mul_sum, sum_boole]
  simp

/-- **The odd-subgroup congruence for `H_a`.** For a coset `X = cH_a` and any `e`,
`∑_{u ∈ X} s(u) s(u^e) ≡ m - 2α(X) - 2α(X^e) (mod 4)`. -/
theorem sum_coset_pow_modEq {c : ZMod p} (hc : c ≠ 0) (e : ℕ) :
    ∑ u ∈ cosetOf c (Ha p), parSign u * parSign (u ^ e) ≡
      (oddPart p : ℤ) - 2 * oddCountZ (cosetOf c (Ha p)) -
        2 * oddCountZ ((cosetOf c (Ha p)).image (· ^ e)) [ZMOD 4] := by
  set X := cosetOf c (Ha p)
  have hm := sum_sign_mul_modEq X parSign (fun u => parSign (u ^ e))
    (fun u _ => parSign_eq u) (fun u _ => parSign_eq _)
  have h1 := sum_parSign X
  have h2 : ∑ u ∈ X, parSign (u ^ e) =
      (X.card : ℤ) - 2 * (Nat.gcd (oddPart p) e * oddCountZ (X.image (· ^ e))) := by
    have : ∀ u : ZMod p, parSign (u ^ e) = 1 - 2 * (if Odd (u ^ e).val then 1 else 0) := by
      intro u; unfold parSign
      rcases Nat.even_or_odd (u ^ e).val with h | h
      · rw [h.neg_one_pow, ite_eq_right (Nat.not_odd_iff_even.2 h)]; ring
      · rw [h.neg_one_pow, ite_eq_left h]; ring
    have hcf := card_filter_pow_Ha hc e (fun y : ZMod p => Odd y.val)
    rw [sum_congr rfl (fun u _ => this u), sum_sub_distrib, ← mul_sum, sum_boole, oddCountZ]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    rw [hcf]; push_cast; ring
  rw [h1, h2, card_coset_Ha hc] at hm
  refine hm.trans ?_
  obtain ⟨q, hq⟩ := (oddPart_odd (prime_two_le (p := p))).of_dvd_nat (Nat.gcd_dvd_left _ e)
  rw [hq]
  exact Int.modEq_iff_dvd.2 ⟨q * oddCountZ (X.image (· ^ e)), by push_cast; ring⟩

end BandParityTower
