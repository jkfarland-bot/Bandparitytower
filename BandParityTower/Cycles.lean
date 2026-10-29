module

public import BandParityTower.Mod8

@[expose] public section

/-!
# Squaring cycles (Proposition 5.6)

* `squaring_cycle`: if squaring permutes a finite set `O` (for instance a cycle of `u ↦ u²` on
  `H`), then `∑_{u ∈ O} s(u) s(u²) = |O| - 2 r_O`, where `r_O` is the number of sign changes, which
  is even; so `O` contributes `|O|` modulo `4`.
* `cube_root_pair`: for a primitive cube root of unity `ω`, the cycle `{ω, ω²}` contributes
  exactly `2`.
* `e_eq_neg_sum`: for `p ≡ 5 (mod 8)`, `e = -∑_{h ∈ H} s(2h) s(P h)` with `P h = -4h²`.
* `rho_three`: for `p ≡ 5 (mod 8)` and `x = ⟨ω⟩`, the contribution
  `ρ₃ = -(s(2h₁) s(P h₁) + s(2h₂) s(P h₂))` of `h₁ = -ω/4`, `h₂ = -ω²/4` is `0` if `x ≢ 2 (mod 4)`,
  `-2` if `x ≡ 2 (mod 8)` and `2` if `x ≡ 6 (mod 8)`.
-/

namespace BandParityTower

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Proposition 5.6 (1).** -/
theorem squaring_cycle' {O : Finset (ZMod p)}
    (hO : Set.BijOn (fun x : ZMod p => x ^ 2) (O : Set (ZMod p)) (O : Set (ZMod p))) :
    ∑ u ∈ O, parSign u * parSign (u ^ 2) =
        O.card - 2 * (O.filter fun u => parSign u ≠ parSign (u ^ 2)).card ∧
      Even (O.filter fun u => parSign u ≠ parSign (u ^ 2)).card ∧
      ∑ u ∈ O, parSign u * parSign (u ^ 2) ≡ O.card [ZMOD 4] := by
  have hσ : ∀ u ∈ O, parSign u * parSign (u ^ 2) = 1 ∨ parSign u * parSign (u ^ 2) = -1 :=
    fun u _ => sign_mul (parSign_eq _) (parSign_eq _)
  have hneg : ∀ u : ZMod p, parSign u * parSign (u ^ 2) = -1 ↔ parSign u ≠ parSign (u ^ 2) := by
    intro u
    rcases parSign_eq u with h | h <;> rcases parSign_eq (u ^ 2) with h' | h' <;>
      rw [h, h'] <;> norm_num
  have hsum := sum_sign_eq O _ hσ
  have hprod := prod_sign_eq O _ hσ
  simp only [hneg] at hsum hprod
  -- the product is a square
  have hsq : ∏ u ∈ O, parSign (u ^ 2) = ∏ u ∈ O, parSign u :=
    prod_nbij (fun x => x ^ 2) (fun x hx => hO.mapsTo hx) (fun x hx y hy h => hO.injOn hx hy h)
      (fun y hy => by obtain ⟨x, hx, rfl⟩ := hO.surjOn hy; exact ⟨x, hx, rfl⟩) (fun _ _ => rfl)
  have h1 : ∏ u ∈ O, parSign u * parSign (u ^ 2) = 1 := by
    rw [prod_mul_distrib, hsq, ← sq, ← prod_pow]
    exact prod_eq_one fun x _ => by rcases parSign_eq x with h | h <;> rw [h] <;> norm_num
  rw [h1] at hprod
  have hev : Even (O.filter fun u => parSign u ≠ parSign (u ^ 2)).card := by
    by_contra h
    rw [Nat.not_even_iff_odd] at h
    rw [h.neg_one_pow] at hprod
    norm_num at hprod
  refine ⟨hsum, hev, ?_⟩
  obtain ⟨j, hj⟩ := hev
  rw [hsum, hj]
  exact Int.modEq_iff_dvd.2 ⟨j, by push_cast; ring⟩

/-! ### Cube roots of unity -/

lemma cube_root_facts (hp2 : p ≠ 2) {ω : ZMod p} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ω ^ 2 = -1 - ω ∧ ω ≠ 0 ∧ ω ≠ -1 ∧ ω ^ 4 = ω := by
  have hq : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by rw [← sub_eq_zero.2 hω]; ring
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω1)
  refine ⟨by linear_combination hq, ?_, ?_, by rw [pow_succ, hω, one_mul]⟩
  · rintro rfl; norm_num at hω
  · rintro rfl
    have : (2 : ZMod p) = 0 := by linear_combination -hω
    exact two_ne_zero' hp2 this

lemma val_neg_eq {x : ZMod p} (hx : x ≠ 0) : (-x).val = p - x.val := by
  rw [ZMod.neg_val, ite_eq_right hx]

lemma val_one_add {x : ZMod p} (hx : x ≠ -1) : (1 + x).val = x.val + 1 := by
  have hv := ZMod.val_lt x
  have hlt : x.val + 1 < p := by
    by_contra h
    apply hx
    have : x.val = p - 1 := by omega
    rw [← ZMod.natCast_zmod_val x, this, Nat.cast_sub hp.out.one_le, ZMod.natCast_self]; ring
  rw [show 1 + x = ((x.val + 1 : ℕ) : ZMod p) by push_cast; rw [ZMod.natCast_zmod_val]; ring,
    ZMod.val_natCast_of_lt hlt]

omit hp in
lemma parSign_eq_ite (x : ZMod p) : parSign x = if x.val % 2 = 0 then 1 else -1 := by
  unfold parSign
  rcases Nat.even_or_odd x.val with h | h
  · rw [h.neg_one_pow, ite_eq_left (Nat.even_iff.1 h)]
  · rw [h.neg_one_pow, ite_eq_right (by rw [Nat.odd_iff] at h; omega)]

/-- **Proposition 5.6 (2).** The cycle `{ω, ω²}` contributes exactly `2`. -/
theorem cube_root_pair' (hp2 : p ≠ 2) {ω : ZMod p} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    parSign ω * parSign (ω ^ 2) + parSign (ω ^ 2) * parSign ((ω ^ 2) ^ 2) = 2 := by
  obtain ⟨h2, h0, hm1, h4⟩ := cube_root_facts hp2 hω hω1
  have hpo : p % 2 = 1 := Nat.odd_iff.1 (odd_prime hp2)
  have hv : (ω ^ 2).val = p - 1 - ω.val := by
    rw [h2, show -1 - ω = -(1 + ω) by ring,
      val_neg_eq (by rintro h; apply hm1; linear_combination h), val_one_add hm1]
    omega
  have hs : parSign (ω ^ 2) = parSign ω := by
    rw [parSign_eq_ite, parSign_eq_ite, hv]
    have hlt := ZMod.val_lt ω
    have : (p - 1 - ω.val) % 2 = ω.val % 2 := by omega
    rw [this]
  rw [← pow_mul, show 2 * 2 = 4 by rfl, h4, hs, parSign_mul_self]; norm_num

/-! ### The order-three pair in `e` -/

/-- For `p ≡ 5 (mod 8)`: `e = -∑_{h ∈ H} s(2h) s(-4h²)`. -/
theorem e_eq_neg_sum (hp8 : p % 8 = 5) {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
    (hpin : χ 2 = gi) :
    (bandSum χ).im = -∑ h ∈ Ha p, parSign (2 * h) * parSign (-4 * h ^ 2) := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  rw [bandSum_im' hχ hp8, cls_gi_eq hχ hp8 hpin, cosetOf,
    sum_image (fun x _ y _ h => mul_left_cancel₀ h20 h), ← sum_neg_distrib]
  refine sum_congr rfl fun h hh => ?_
  have hh0 := ne_zero_of_mem_Ha hh
  have h40 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h20 h20
  rw [show (2 * h) ^ 2 = -(-4 * h ^ 2) by ring,
    parSign_neg hp2 (mul_ne_zero (neg_ne_zero.2 h40) (pow_ne_zero 2 hh0)), mul_neg]

/-- `⟨y/2⟩`. -/
lemma val_div_two (hp2 : p ≠ 2) (y : ZMod p) :
    (y / 2).val = if y.val % 2 = 0 then y.val / 2 else (y.val + p) / 2 := by
  have h20 := two_ne_zero' (p := p) hp2
  have hpo : p % 2 = 1 := Nat.odd_iff.1 (odd_prime hp2)
  have hv := ZMod.val_lt y
  set c := if y.val % 2 = 0 then y.val / 2 else (y.val + p) / 2
  have hc : c < p := by simp only [c]; split_ifs <;> omega
  have h2c : ((2 * c : ℕ) : ZMod p) = y := by
    rw [← ZMod.natCast_zmod_val y]
    simp only [c]
    split_ifs with h
    · congr 1; omega
    · rw [show 2 * ((y.val + p) / 2) = y.val + p by omega]; push_cast; simp
  have : y / 2 = (c : ZMod p) := by
    rw [← h2c, div_eq_iff h20]; push_cast; ring
  rw [this, ZMod.val_natCast_of_lt hc]

/-- `⟨y/4⟩` for `p ≡ 1 (mod 4)`. -/
lemma val_div_four (hp4 : p % 4 = 1) (y : ZMod p) :
    (y / 4).val = if y.val % 4 = 0 then y.val / 4 else if y.val % 4 = 3 then (y.val + p) / 4
      else if y.val % 4 = 2 then (y.val + 2 * p) / 4 else (y.val + 3 * p) / 4 := by
  have hp2 : p ≠ 2 := by omega
  have h20 := two_ne_zero' (p := p) hp2
  have h40 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h20 h20
  have hv := ZMod.val_lt y
  set c := if y.val % 4 = 0 then y.val / 4 else if y.val % 4 = 3 then (y.val + p) / 4
      else if y.val % 4 = 2 then (y.val + 2 * p) / 4 else (y.val + 3 * p) / 4
  have hc : c < p := by simp only [c]; split_ifs <;> omega
  have h4c : ((4 * c : ℕ) : ZMod p) = y := by
    rw [← ZMod.natCast_zmod_val y]
    simp only [c]
    split_ifs with h h' h''
    · congr 1; omega
    · rw [show 4 * ((y.val + p) / 4) = y.val + p by omega]; push_cast; simp
    · rw [show 4 * ((y.val + 2 * p) / 4) = y.val + 2 * p by omega]; push_cast; simp
    · rw [show 4 * ((y.val + 3 * p) / 4) = y.val + 3 * p by omega]; push_cast; simp
  have : y / 4 = (c : ZMod p) := by
    rw [← h4c, div_eq_iff h40]; push_cast; ring
  rw [this, ZMod.val_natCast_of_lt hc]

omit hp in
/-- The arithmetic behind Proposition 5.6 (3). -/
lemma rho_arith (p x : ℕ) (hp8 : p % 8 = 5) (_hx0 : 0 < x) (hx : x + 1 < p) :
    -((if (if (p - x) % 2 = 0 then (p - x) / 2 else (p - x + p) / 2) % 2 = 0 then (1 : ℤ) else -1) *
      (if (if (x + 1) % 4 = 0 then (x + 1) / 4 else if (x + 1) % 4 = 3 then (x + 1 + p) / 4
        else if (x + 1) % 4 = 2 then (x + 1 + 2 * p) / 4 else (x + 1 + 3 * p) / 4) % 2 = 0
        then 1 else -1) +
      (if (if (x + 1) % 2 = 0 then (x + 1) / 2 else (x + 1 + p) / 2) % 2 = 0 then (1 : ℤ) else -1) *
      (if (if (p - x) % 4 = 0 then (p - x) / 4 else if (p - x) % 4 = 3 then (p - x + p) / 4
        else if (p - x) % 4 = 2 then (p - x + 2 * p) / 4 else (p - x + 3 * p) / 4) % 2 = 0
        then 1 else -1)) =
      if x % 4 ≠ 2 then 0 else if x % 8 = 2 then -2 else 2 := by
  obtain ⟨r, hr⟩ : ∃ r, r = x % 8 := ⟨_, rfl⟩
  have hr8 : r < 8 := by omega
  interval_cases r <;> simp (disch := omega) only [ite_eq_left, ite_eq_right] <;> norm_num

/-- **Proposition 5.6 (3).** -/
theorem rho_three' (hp8 : p % 8 = 5) {ω : ZMod p} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    -(parSign (-ω / 2) * parSign (-ω ^ 2 / 4) + parSign (-ω ^ 2 / 2) * parSign (-ω / 4)) =
      if ω.val % 4 ≠ 2 then 0 else if ω.val % 8 = 2 then -2 else 2 := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨h2, h0, hm1, -⟩ := cube_root_facts hp2 hω hω1
  have hx := ZMod.val_lt ω
  have hx0 : ω.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  have hv1 : (-ω).val = p - ω.val := val_neg_eq h0
  have hv2 : (-ω ^ 2).val = ω.val + 1 := by
    rw [h2, show -(-1 - ω) = 1 + ω by ring, val_one_add hm1]
  have hp4 : p % 4 = 1 := by omega
  rw [parSign_eq_ite, parSign_eq_ite, parSign_eq_ite, parSign_eq_ite, val_div_two hp2,
    val_div_two hp2, val_div_four hp4, val_div_four hp4, hv1, hv2]
  have hxm1 : ω.val + 1 < p := by
    by_contra h
    apply hm1
    have : ω.val = p - 1 := by omega
    rw [← ZMod.natCast_zmod_val ω, this, Nat.cast_sub hp.out.one_le, ZMod.natCast_self]; ring
  exact rho_arith p ω.val hp8 (by omega) hxm1

end BandParityTower
