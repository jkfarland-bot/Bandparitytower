module

public import BandParityTower.Half
public import BandParityTower.Main

@[expose] public section

/-!
# The tower

For a prime `p` with `a = v₂(p - 1)` and `m = (p - 1)/2^a`:

* `fTower_modEq` (**the band-parity tower**): `f_a ≡ m (mod 4)`, and `towerBand_eq` gives `f_a`
  the band-sum form `∑_{0 < n < p/2, n ∈ ± H_a} η(n) (-1)^{⌊n²/p⌋}`.
* `lag_two` (**the doubling count**): for `p ≡ 1 (mod 4)`, `∑_{u ∈ 2H_a} s(u) s(2u) = 2N_a - m`.
* `eTower_modEq` (**the imaginary coordinate at every level**): `e_a ≡ 2N_a - m (mod 4)`.
* `collapse`: if `2` is a `2^{a-1}`-th power residue, `e_a = ± f_a` and `2` is a `2^a`-th power
  residue iff `N_a` is odd.
-/

namespace BandParityTower

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Membership in `± cH_a` -/

lemma cosetOf_one (S : Finset (ZMod p)) : cosetOf 1 S = S := by simp [cosetOf]

lemma pm_coset_iff (hp2 : p ≠ 2) {c : ZMod p} (hc : c ≠ 0) (n : ZMod p) :
    (n ∈ cosetOf c (Ha p) ∨ -n ∈ cosetOf c (Ha p)) ↔ (c⁻¹ * n) ^ (2 * oddPart p) = 1 := by
  rw [mem_coset_iff hc, mem_coset_iff hc, mul_neg, neg_pow, neg_one_pow_oddPart hp2,
    neg_one_mul, pow_mul']
  constructor
  · rintro (h | h)
    · rw [h, one_pow]
    · rw [show (c⁻¹ * n) ^ oddPart p = -1 from neg_eq_iff_eq_neg.1 h]; norm_num
  · intro h
    rcases mul_self_eq_one_iff.1 (show (c⁻¹ * n) ^ oddPart p * (c⁻¹ * n) ^ oddPart p = 1 by
      rw [← sq]; exact h) with h' | h'
    · exact Or.inl h'
    · right; rw [h', neg_neg]

lemma pm_Ha_iff (hp2 : p ≠ 2) (n : ZMod p) :
    (n ∈ Ha p ∨ -n ∈ Ha p) ↔ n ^ (2 * oddPart p) = 1 := by
  have h := pm_coset_iff hp2 (one_ne_zero (α := ZMod p)) n
  simp only [inv_one, one_mul, cosetOf_one] at h
  exact h

/-! ### Squaring and doubling on cosets -/

lemma sq_injOn_coset (hp2 : p ≠ 2) {c : ZMod p} (hc : c ≠ 0) :
    Set.InjOn (fun x : ZMod p => x ^ 2) (cosetOf c (Ha p) : Set (ZMod p)) := by
  intro x hx y hy h
  simp only at h
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h' | h'
  · exact h'
  · exfalso
    rw [mem_coe] at hx hy
    exact neg_not_mem_coset hp2 hc hy (h' ▸ hx)

lemma sq_mapsTo_coset {c : ZMod p} (hc : c ≠ 0) :
    Set.MapsTo (fun x : ZMod p => x ^ 2) (cosetOf c (Ha p) : Set (ZMod p))
      (cosetOf (c ^ 2) (Ha p) : Set (ZMod p)) := by
  intro x hx
  rw [mem_coe, mem_cosetOf hc] at hx
  rw [mem_coe, mem_cosetOf (pow_ne_zero 2 hc)]
  have := mul_mem_Ha hx hx
  simpa [sq, mul_inv, mul_mul_mul_comm] using this

lemma sq_bijOn_coset (hp2 : p ≠ 2) {c : ZMod p} (hc : c ≠ 0) :
    Set.BijOn (fun x : ZMod p => x ^ 2) (cosetOf c (Ha p) : Set (ZMod p))
      (cosetOf (c ^ 2) (Ha p) : Set (ZMod p)) :=
  bijOn_of_injOn_card (sq_mapsTo_coset hc) (sq_injOn_coset hp2 hc)
    (by rw [card_coset_Ha hc, card_coset_Ha (pow_ne_zero 2 hc)])

lemma mul_bijOn_coset {c d : ZMod p} (hc : c ≠ 0) (hd : d ≠ 0) :
    Set.BijOn (fun x : ZMod p => d * x) (cosetOf c (Ha p) : Set (ZMod p))
      (cosetOf (d * c) (Ha p) : Set (ZMod p)) := by
  refine bijOn_of_injOn_card ?_ (fun x _ y _ h => mul_left_cancel₀ hd h)
    (by rw [card_coset_Ha hc, card_coset_Ha (mul_ne_zero hd hc)])
  intro x hx
  rw [mem_coe, mem_cosetOf hc] at hx
  rw [mem_coe, mem_cosetOf (mul_ne_zero hd hc)]
  have : (d * c)⁻¹ * (d * x) = c⁻¹ * x := by
    rw [mul_inv, mul_comm d⁻¹, mul_assoc, ← mul_assoc d⁻¹, inv_mul_cancel₀ hd, one_mul]
  simpa only [this] using hx

/-! ### The band-parity tower -/

/-- **The band-parity tower** (Corollary 4.4). `f_a ≡ m (mod 4)`. -/
theorem fTower_modEq (hp2 : p ≠ 2) : fTower p ≡ oddPart p [ZMOD 4] := by
  have hb : Set.BijOn (fun x : ZMod p => x ^ 2) (Ha p : Set (ZMod p)) (Ha p : Set (ZMod p)) := by
    have := sq_bijOn_coset hp2 (one_ne_zero (α := ZMod p))
    simpa [cosetOf_one] using this
  have := matching_indep' (Ha p) (Ha p) (fun x => x ^ 2) id hb (Set.bijOn_id _) parSign parSign
    (fun x _ => parSign_eq x) (fun x _ => parSign_eq x)
  unfold fTower
  refine this.trans ?_
  simp only [id, parSign_mul_self, sum_const, nsmul_eq_mul, mul_one, card_Ha]
  rfl

/-- The band-sum form of `f_a`: `∑_{0 < n < p/2, n ∈ ± H_a} η(n) (-1)^{⌊n²/p⌋} = f_a`, where
`η = 1` on `H_a` and `-1` on `-H_a`. -/
theorem towerBand_eq (hp2 : p ≠ 2) :
    ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p ∧ n ^ (2 * oddPart p) = 1),
      (if n ^ oddPart p = 1 then 1 else -1) * (-1 : ℤ) ^ band n = fTower p := by
  have h := pairBandSum_eq hp2 (Ha p) zero_not_mem_Ha
    (fun x hx => by
      simpa [cosetOf_one] using neg_not_mem_coset hp2 (one_ne_zero (α := ZMod p))
        (by simpa [cosetOf_one] using hx))
    even_two two_ne_zero
  rw [fTower, ← h, pairBandSum]
  refine sum_congr ?_ fun n _ => ?_
  · ext n; simp only [mem_filter, mem_univ, true_and, pm_Ha_iff hp2]
  · simp [mem_Ha_iff, bandSignE, band]

/-! ### The doubling count -/

lemma parSign_two_mul (hp2 : p ≠ 2) {x : ZMod p} (hx : 2 * x.val < p) : parSign (2 * x) = 1 :=
  parSign_two_mul_of_lt hp2 hx

/-- **The doubling count** (Proposition 3.5 at `c = 2`). For `p ≡ 1 (mod 4)`,
`∑_{u ∈ 2H_a} s(u) s(2u) = 2N_a - m`. -/
theorem lag_two (hp4 : p % 4 = 1) :
    ∑ u ∈ cosetOf 2 (Ha p), parSign u * parSign (2 * u) = 2 * (Na p : ℤ) - oddPart p := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  have ha : 1 ≤ twoVal p := le_trans (by norm_num) (twoVal_ge_two hp4 prime_two_le)
  set X := cosetOf 2 (Ha p)
  set rep := univ.filter (fun n : ZMod p => 2 * n.val < p ∧ (n ∈ X ∨ -n ∈ X))
  have hX0 := zero_not_mem_coset (p := p) h20
  have hdisj : ∀ x ∈ X, -x ∉ X := fun x hx => neg_not_mem_coset hp2 h20 hx
  -- reduce to the representatives
  have h1 := sum_eq_sum_half_pair hp2 X hX0 hdisj (fun u => parSign u * parSign (2 * u))
  have h1' : ∑ n ∈ rep, (if n ∈ X then parSign n * parSign (2 * n)
      else parSign (-n) * parSign (2 * -n)) = ∑ n ∈ rep, parSign n := by
    refine sum_congr rfl fun n hn => ?_
    have hn' := (mem_filter.1 hn).2
    have hn0 : n ≠ 0 := by
      rintro rfl; rcases hn'.2 with h | h
      · exact hX0 h
      · rw [neg_zero] at h; exact hX0 h
    rw [parSign_two_mul hp2 hn'.1]
    split_ifs
    · ring
    · rw [mul_neg, parSign_neg hp2 hn0, parSign_neg hp2 (mul_ne_zero h20 hn0),
        parSign_two_mul hp2 hn'.1]; ring
  rw [h1, h1', sum_parSign]
  -- the number of representatives
  have hcard : rep.card = oddPart p := by
    have := sum_eq_sum_half_pair hp2 X hX0 hdisj (fun _ => (1 : ℕ))
    simp only [sum_const, smul_eq_mul, mul_one, ite_self] at this
    rw [← this, card_coset_Ha h20]
  -- the even representatives are the doubles of the counted residues
  have heven : (rep.filter fun n => ¬ Odd n.val).card = Na p := by
    unfold Na powResCount
    symm
    refine card_nbij' (fun r => ((2 * r : ℕ) : ZMod p)) (fun n => n.val / 2) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [mem_coe, mem_filter, mem_range] at hr
      obtain ⟨hrp, hr0, hr4, hry⟩ := hr
      have hv : (((2 * r : ℕ) : ZMod p)).val = 2 * r := ZMod.val_natCast_of_lt (by omega)
      simp only [rep, mem_coe, mem_filter, mem_univ, true_and, hv]
      refine ⟨⟨by omega, ?_⟩, by rw [Nat.not_odd_iff_even]; exact even_two_mul r⟩
      rw [pm_coset_iff hp2 h20, Nat.cast_mul, Nat.cast_two, ← mul_assoc, inv_mul_cancel₀ h20,
        one_mul]
      have hr0' : (r : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; exact absurd (Nat.le_of_dvd hr0 h) (by omega)
      exact (exists_pow_pred_iff ha hr0').1 hry
    · intro n hn
      simp only [rep, mem_coe, mem_filter, mem_univ, true_and] at hn
      obtain ⟨⟨hl, hpm⟩, hev⟩ := hn
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨r, hr⟩ := hev
      have hn0 : n ≠ 0 := by
        rintro rfl; rcases hpm with h | h
        · exact hX0 h
        · rw [neg_zero] at h; exact hX0 h
      have hr0 : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · exfalso; apply hn0; rw [← ZMod.val_eq_zero, hr, h]
        · exact h
      have hnr : n = 2 * (r : ZMod p) := by
        rw [← ZMod.natCast_zmod_val n, hr]; push_cast; ring
      simp only [mem_coe, mem_filter, mem_range]
      refine ⟨by omega, by omega, by omega, ?_⟩
      rw [show n.val / 2 = r by omega]
      have hr0' : (r : ZMod p) ≠ 0 := by rintro h; rw [h, mul_zero] at hnr; exact hn0 hnr
      rw [exists_pow_pred_iff ha hr0']
      rw [pm_coset_iff hp2 h20, hnr, ← mul_assoc, inv_mul_cancel₀ h20, one_mul] at hpm
      exact hpm
    · intro r hr
      simp only [mem_coe, mem_filter, mem_range] at hr
      simp only
      rw [ZMod.val_natCast_of_lt (by omega)]; omega
    · intro n hn
      simp only [rep, mem_coe, mem_filter, mem_univ, true_and] at hn
      obtain ⟨-, hev⟩ := hn
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨r, hr⟩ := hev
      simp only
      rw [show n.val / 2 = r by omega, ← ZMod.natCast_zmod_val n, hr]; push_cast; ring
  have hsplit := card_filter_add_card_filter_not (s := rep) (p := fun n : ZMod p => Odd n.val)
  unfold oddCountZ
  rw [hcard, heven] at hsplit
  rw [hcard]
  have : ((rep.filter fun n : ZMod p => Odd n.val).card : ℤ) = oddPart p - Na p := by
    have := congrArg (fun k : ℕ => (k : ℤ)) hsplit
    push_cast at this; linarith
  rw [this]; ring

/-- **The imaginary coordinate at every level** (Theorem 4.5). For `p ≡ 1 (mod 4)`,
`e_a ≡ 2N_a - m (mod 4)`. -/
theorem eTower_modEq (hp4 : p % 4 = 1) : eTower p ≡ 2 * (Na p : ℤ) - oddPart p [ZMOD 4] := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  have hsq := sq_bijOn_coset hp2 h20
  have hdb := mul_bijOn_coset (d := 2) h20 h20
  rw [show (2 : ZMod p) * 2 = 2 ^ 2 by ring] at hdb
  have := matching_indep' (cosetOf 2 (Ha p)) (cosetOf (2 ^ 2) (Ha p)) (fun x => x ^ 2)
    (fun x => 2 * x) hsq hdb parSign parSign (fun x _ => parSign_eq x) (fun x _ => parSign_eq x)
  unfold eTower
  exact this.trans (by rw [lag_two hp4])

/-- The band-sum form of `e_a`: `∑_{0 < n < p/2, n ∈ ± 2H_a} σ(n) (-1)^{⌊n²/p⌋} = e_a`, where
`σ = 1` on `2H_a` and `-1` on `-2H_a`. -/
theorem eTowerBand_eq (hp2 : p ≠ 2) :
    ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p ∧ (n / 2) ^ (2 * oddPart p) = 1),
      (if (n / 2) ^ oddPart p = 1 then 1 else -1) * (-1 : ℤ) ^ band n = eTower p := by
  have h20 := two_ne_zero' (p := p) hp2
  have h := pairBandSum_eq hp2 (cosetOf 2 (Ha p)) (zero_not_mem_coset h20)
    (fun x hx => neg_not_mem_coset hp2 h20 hx) even_two two_ne_zero
  rw [eTower, ← h, pairBandSum]
  refine sum_congr ?_ fun n _ => ?_
  · ext n
    simp only [mem_filter, mem_univ, true_and, pm_coset_iff hp2 h20, div_eq_inv_mul]
  · simp [mem_coset_iff h20, bandSignE, band, div_eq_inv_mul]

/-! ### The collapse -/

lemma cosetOf_eq_of_mem {c : ZMod p} (hc : c ∈ Ha p) : cosetOf c (Ha p) = Ha p := by
  have hc0 := ne_zero_of_mem_Ha hc
  ext x
  rw [mem_cosetOf hc0]
  constructor
  · intro h; have := mul_mem_Ha hc h; rwa [← mul_assoc, mul_inv_cancel₀ hc0, one_mul] at this
  · intro h; exact mul_mem_Ha (inv_mem_Ha hc) h

/-- **The collapse** (Corollary 4.7). Let `p ≡ 1 (mod 4)` and suppose `2` is a `2^{a-1}`-th power
residue. Then `e_a = f_a` if `2 ∈ H_a` and `e_a = -f_a` otherwise, and `2` is a `2^a`-th power
residue iff `N_a` is odd. -/
theorem collapse (hp4 : p % 4 = 1) (h2 : ∃ y : ZMod p, y ^ 2 ^ (twoVal p - 1) = 2) :
    ((2 : ZMod p) ∈ Ha p → eTower p = fTower p) ∧
    ((2 : ZMod p) ∉ Ha p → eTower p = -fTower p) ∧
    ((∃ y : ZMod p, y ^ 2 ^ twoVal p = 2) ↔ Odd (Na p)) := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  have ha : 1 ≤ twoVal p := le_trans (by norm_num) (twoVal_ge_two hp4 prime_two_le)
  have h2m : (2 : ZMod p) ^ (2 * oddPart p) = 1 := (exists_pow_pred_iff ha h20).1 h2
  have hpos : (2 : ZMod p) ∈ Ha p → eTower p = fTower p := by
    intro h; unfold eTower fTower; rw [cosetOf_eq_of_mem h]
  have hneg : (2 : ZMod p) ∉ Ha p → eTower p = -fTower p := by
    intro h
    have hm2 : -(2 : ZMod p) ∈ Ha p := by
      have := (pm_Ha_iff hp2 2).2 h2m; tauto
    have hcos : cosetOf 2 (Ha p) = (Ha p).image (fun x => -x) := by
      ext x
      rw [mem_cosetOf h20, mem_image]
      constructor
      · intro hx
        refine ⟨-x, ?_, neg_neg x⟩
        have := mul_mem_Ha hm2 hx
        rwa [neg_mul, ← mul_assoc, mul_inv_cancel₀ h20, one_mul] at this
      · rintro ⟨y, hy, rfl⟩
        have := mul_mem_Ha (inv_mem_Ha hm2) hy
        rwa [inv_neg, neg_mul, ← mul_neg] at this
    unfold eTower fTower
    rw [hcos, sum_image (fun x _ y _ h => neg_injective h), ← sum_neg_distrib]
    refine sum_congr rfl fun x hx => ?_
    rw [parSign_neg hp2 (ne_zero_of_mem_Ha hx), neg_sq]; ring
  refine ⟨hpos, hneg, ?_⟩
  have hm := oddPart_odd (prime_two_le (p := p))
  have he := eTower_modEq hp4
  have hf := fTower_modEq hp2
  rw [exists_pow_top_iff h20, ← mem_Ha_iff]
  by_cases h : (2 : ZMod p) ∈ Ha p
  · simp only [h, true_iff]
    have := (hpos h ▸ he).symm.trans hf
    rw [Int.ModEq] at this
    by_contra hN
    rw [Nat.not_odd_iff_even] at hN
    obtain ⟨j, hj⟩ := hN
    obtain ⟨q, hq⟩ := hm
    rw [hj, hq] at this; push_cast at this; omega
  · simp only [h, false_iff]
    have hf' : -fTower p ≡ -(oddPart p : ℤ) [ZMOD 4] := hf.neg
    have := (hneg h ▸ he).symm.trans hf'
    rw [Int.ModEq] at this
    intro hN
    obtain ⟨j, hj⟩ := hN
    obtain ⟨q, hq⟩ := hm
    rw [hj, hq] at this; push_cast at this; omega

end BandParityTower
