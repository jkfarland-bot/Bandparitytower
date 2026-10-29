module

public import BandParityTower.Quartic

@[expose] public section

/-!
# The companion law at `p ≡ 1 (mod 8)`

For a prime `p ≡ 1 (mod 8)` and either quartic character `χ` (which is then even), write
`H = {x : 2⟨x⟩ < p}`, `b(x) = ⌊⟨x⟩²/p⌋` and `(x/p)` for the Legendre symbol. The proof runs:

* termwise, `Re (χ(x) (-1)^{b(x)}) ≡ Re χ(x) + (1 + (x/p)) b(x)` and
  `Im (χ(x) (-1)^{b(x)}) ≡ Im χ(x) + (1 - (x/p)) b(x) (mod 4)`; since `χ` is even its half sum
  vanishes, so `Re 𝒞 ≡ ∑_H b + X` and `Im 𝒞 ≡ ∑_H b - X` with `X = ∑_H (x/p) b(x)`
  (`bandSum_re_im_modEq`);
* `⟨x⟩² = p b(x) + ⟨x²⟩`, and the twist `x ↦ ι x` by a square root `ι` of `-1` (a square, since
  `p ≡ 1 (mod 8)`) gives `4 ∑_H ⟨x²⟩ = p (p - 1)` and `∑_H (x/p) ⟨x²⟩ = 0`; hence
  `3 ∑_H b = 4 q (2 q - 1)` with `p = 8 q + 1` (`sum_band_modEq`), and `p X = M₂ = ∑_H (x/p) ⟨x⟩²`;
* the reflection `k ↦ 2k` (`k ≤ 2q`), `k ↦ p - 2k` (`k > 2q`) of `[0, 4q]` gives
  `3 M₂ = -p ∑_{2q < k ≤ 4q} (k/p) (p - 4k)` (`three_mul_sum_legendre_sq`), whence
  `3 X ≡ κ (mod 4)` and `X ≡ κ (mod 4)` since `κ` is even (`sum_legendre_band_modEq`).
-/

namespace BandParityTower
open Finset

/-! ### Elementary congruences and sums -/

lemma neg_one_pow_modEq_four (w : ℕ) : (-1 : ℤ) ^ w ≡ 1 + 2 * w [ZMOD 4] := by
  rcases Nat.even_or_odd w with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [Even.neg_one_pow ⟨j, rfl⟩]
    exact Int.modEq_iff_dvd.2 ⟨j, by push_cast; ring⟩
  · rw [Odd.neg_one_pow ⟨j, rfl⟩]
    exact Int.modEq_iff_dvd.2 ⟨j + 1, by push_cast; ring⟩

lemma sign_mul_neg_one_pow_modEq {a : ℤ} (ha : a = 1 ∨ a = -1) (w : ℕ) :
    a * (-1 : ℤ) ^ w ≡ a + 2 * w [ZMOD 4] := by
  have h := neg_one_pow_modEq_four w
  rcases ha with rfl | rfl
  · rw [one_mul]; exact h
  · rw [neg_one_mul]
    exact h.neg.trans (Int.modEq_iff_dvd.2 ⟨w, by ring⟩)

lemma six_mul_sum_sq (N : ℕ) :
    6 * ∑ v ∈ range N, (v : ℤ) ^ 2 = ((N : ℤ) - 1) * N * (2 * N - 1) := by
  induction N with
  | zero => simp
  | succ n ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Squares, bands and the twist by `√-1` -/

/-- `⟨x⟩² = p b(x) + ⟨x²⟩`. -/
lemma val_sq_eq (x : ZMod p) :
    (x.val : ℤ) ^ 2 = p * (band x : ℤ) + ((x ^ 2).val : ℤ) := by
  have hsq : (x ^ 2).val = x.val ^ 2 % p := by rw [sq, ZMod.val_mul, sq]
  rw [hsq, band]
  have := Nat.div_add_mod (x.val ^ 2) p
  exact_mod_cast this.symm

lemma val_add_val_neg (y : ZMod p) :
    (y.val : ℤ) + ((-y).val : ℤ) = if y = 0 then 0 else (p : ℤ) := by
  by_cases hy : y = 0
  · subst hy; simp
  · simp only [hy, ↓reduceIte]
    rw [val_neg_of_ne_zero hy, Nat.cast_sub (ZMod.val_lt y).le]; ring

/-- A square root `ι` of `-1` which is itself a square (`p ≡ 1 (mod 8)`). -/
lemma exists_sqrt_neg_one (hp8 : p % 8 = 1) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) :
    ∃ ι : ZMod p, ι ^ 2 = -1 ∧ quadraticChar (ZMod p) ι = 1 := by
  obtain ⟨ι, hι⟩ := ZMod.exists_sq_eq_neg_one_iff.2 (show p % 4 ≠ 3 by omega)
  have hι2 : ι ^ 2 = -1 := by rw [hι, sq]
  have hι0 : ι ≠ 0 := by rintro rfl; simp at hι2
  refine ⟨ι, hι2, quadraticChar_of_char_one hχ hι0 ?_⟩
  have h1 : χ ι * χ ι = 1 := by
    rw [← map_mul, ← sq, hι2, quartic_apply_neg_one_of_one χ hχ hp8]
  exact mul_self_eq_one_iff.1 h1

/-- The twist `x ↦ ι x` with `ι² = -1`: `2 ∑ φ(x) ⟨x²⟩ = p ∑_{x ≠ 0} φ(x)`. -/
lemma two_mul_sum_twist (φ : ZMod p → ℤ) {ι : ZMod p} (hι : ι ^ 2 = -1)
    (hφ : ∀ x, φ (ι * x) = φ x) :
    2 * ∑ x, φ x * ((x ^ 2).val : ℤ) = p * ∑ x, (if x = 0 then 0 else φ x) := by
  have hι0 : ι ≠ 0 := by rintro rfl; simp at hι
  have h1 : ∑ x, φ x * (((-(x ^ 2))).val : ℤ) = ∑ x, φ x * ((x ^ 2).val : ℤ) :=
    Fintype.sum_equiv (Equiv.mulLeft₀ ι hι0) _ _ fun x => by
      simp only [Equiv.mulLeft₀_apply, hφ, mul_pow, hι, neg_one_mul]
  have h2 : 2 * ∑ x, φ x * ((x ^ 2).val : ℤ) =
      ∑ x, φ x * ((x ^ 2).val : ℤ) + ∑ x, φ x * (((-(x ^ 2))).val : ℤ) := by
    rw [two_mul, h1]
  rw [h2, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [← mul_add, val_add_val_neg]
  by_cases hx : x = 0
  · simp [hx]
  · have : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    simp [hx, this]; ring

/-- Half-range form of the twist. -/
lemma four_mul_sum_half_twist (hp2 : p ≠ 2) (φ : ZMod p → ℤ) {ι : ZMod p} (hι : ι ^ 2 = -1)
    (hφ : ∀ x, φ (ι * x) = φ x) (hneg : ∀ x, φ (-x) = φ x) :
    4 * ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), φ x * ((x ^ 2).val : ℤ) =
      p * ∑ x, (if x = 0 then 0 else φ x) := by
  have h := sum_eq_two_nsmul_half hp2 (fun x => φ x * ((x ^ 2).val : ℤ)) (by simp)
    (fun x => by simp [hneg])
  rw [← two_mul_sum_twist φ hι hφ, h, two_nsmul]
  ring

/-- `4 ∑_{x ∈ H} ⟨x²⟩ = p (p - 1)`. -/
lemma four_mul_sum_half_val_sq (hp8 : p % 8 = 1) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) :
    4 * ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), ((x ^ 2).val : ℤ) =
      p * (p - 1) := by
  obtain ⟨ι, hι, -⟩ := exists_sqrt_neg_one hp8 hχ
  have h := four_mul_sum_half_twist (by omega) (fun _ => 1) hι (fun _ => rfl) (fun _ => rfl)
  simp only [one_mul] at h
  rw [h]
  congr 1
  rw [Finset.sum_ite]
  simp [Finset.filter_ne', Nat.cast_sub hp.out.one_lt.le]

/-- `∑_{x ∈ H} (x/p) ⟨x²⟩ = 0`. -/
lemma sum_half_legendre_val_sq (hp8 : p % 8 = 1) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) :
    ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p),
      quadraticChar (ZMod p) x * ((x ^ 2).val : ℤ) = 0 := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ι, hι, hι1⟩ := exists_sqrt_neg_one hp8 hχ
  have h := four_mul_sum_half_twist hp2 (fun x => quadraticChar (ZMod p) x) hι
    (fun x => by simp [map_mul, hι1]) (fun x => quadraticChar_neg (by omega) x)
  have h0 : ∑ x : ZMod p, (if x = 0 then 0 else quadraticChar (ZMod p) x) = 0 := by
    have : ∀ x : ZMod p,
        (if x = 0 then 0 else quadraticChar (ZMod p) x) = quadraticChar (ZMod p) x := by
      intro x; by_cases hx : x = 0 <;> simp [hx]
    simp only [this]; exact quadraticChar_sum_zero (ringChar_ne_two hp2)
  rw [h0, mul_zero] at h
  linarith

/-- `∑_{x ∈ H} ⟨x⟩² = ∑_{v ≤ (p - 1)/2} v²` as a sum over `ℕ`. -/
lemma sum_half_val_sq_eq (q : ℕ) (hq : p = 8 * q + 1) (g : ℕ → ℤ) :
    ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), g x.val =
      ∑ v ∈ range (4 * q + 1), g v := by
  rw [sum_filter_val (fun v => 2 * v < p) g]
  congr 1
  ext v; simp only [mem_filter, mem_range]; omega

/-- **The band total.** `∑_{x ∈ H} b(x) ≡ 0 (mod 4)`; indeed `3 ∑_H b = 4 q (2 q - 1)`. -/
lemma sum_band_modEq (hp8 : p % 8 = 1) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) :
    ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), (band x : ℤ) ≡ 0 [ZMOD 4] := by
  obtain ⟨q, hq⟩ : ∃ q, p = 8 * q + 1 := ⟨p / 8, by omega⟩
  set H := univ.filter (fun x : ZMod p => 2 * x.val < p) with hH
  set S := ∑ x ∈ H, (band x : ℤ)
  set R := ∑ x ∈ H, ((x ^ 2).val : ℤ)
  have E1 : ∑ x ∈ H, (x.val : ℤ) ^ 2 = p * S + R := by
    rw [sum_congr rfl fun x _ => val_sq_eq x, sum_add_distrib, ← mul_sum]
  have E2 := six_mul_sum_sq (4 * q + 1)
  rw [← sum_half_val_sq_eq q hq (fun v => (v : ℤ) ^ 2)] at E2
  have E3 := four_mul_sum_half_val_sq hp8 hχ
  have hpq : (p : ℤ) = 8 * q + 1 := by rw [hq]; push_cast; ring
  rw [E1] at E2
  rw [hpq] at E2 E3
  push_cast at E2
  have key : ((8 * q + 1 : ℤ)) * (12 * (3 * S - 4 * q * (2 * q - 1))) = 0 := by
    linear_combination 6 * E2 - 9 * E3
  have hp0 : (8 * q + 1 : ℤ) ≠ 0 := by positivity
  have k2 : 3 * S = 4 * q * (2 * q - 1) := by
    have := (mul_eq_zero.1 key).resolve_left hp0
    linarith
  exact Int.modEq_iff_dvd.2 ⟨q * (2 * q - 1) - S, by linarith⟩

/-! ### The termwise congruence and the half sum of `χ` -/

lemma re_mul_neg_one_pow (z : GaussianInt) (w : ℕ) :
    (z * (-1) ^ w).re = z.re * (-1 : ℤ) ^ w := by
  have hc : ((-1 : GaussianInt) ^ w) = (((-1 : ℤ) ^ w : ℤ) : GaussianInt) := by push_cast; rfl
  rw [hc, Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]; ring

lemma im_mul_neg_one_pow (z : GaussianInt) (w : ℕ) :
    (z * (-1) ^ w).im = z.im * (-1 : ℤ) ^ w := by
  have hc : ((-1 : GaussianInt) ^ w) = (((-1 : ℤ) ^ w : ℤ) : GaussianInt) := by push_cast; rfl
  rw [hc, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]; ring

/-- Termwise: `Re (χ(x)(-1)^{b(x)}) ≡ Re χ(x) + (1 + (x/p)) b(x)` and
`Im (χ(x)(-1)^{b(x)}) ≡ Im χ(x) + (1 - (x/p)) b(x) (mod 4)`. -/
lemma term_modEq {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4) (x : ZMod p) :
    (χ x * (-1) ^ band x).re ≡
        (χ x).re + (1 + quadraticChar (ZMod p) x) * (band x : ℤ) [ZMOD 4] ∧
      (χ x * (-1) ^ band x).im ≡
        (χ x).im + (1 - quadraticChar (ZMod p) x) * (band x : ℤ) [ZMOD 4] := by
  rw [re_mul_neg_one_pow, im_mul_neg_one_pow]
  by_cases hx : x = 0
  · subst hx; simp [band]
  have h1 := sign_mul_neg_one_pow_modEq (a := 1) (Or.inl rfl) (band x)
  have h2 := sign_mul_neg_one_pow_modEq (a := -1) (Or.inr rfl) (band x)
  rcases quartic_values χ hχ hx with h | h | h | h
  · rw [quadraticChar_of_char_one hχ hx (Or.inl h), h]
    refine ⟨?_, ?_⟩
    · convert h1 using 2 <;> simp
    · simp
  · rw [quadraticChar_of_char_gi hχ hx (Or.inl h), h]
    refine ⟨?_, ?_⟩
    · simp [gi]
    · convert h1 using 2 <;> simp [gi]
  · rw [quadraticChar_of_char_one hχ hx (Or.inr h), h]
    refine ⟨?_, ?_⟩
    · convert h2 using 2 <;> simp
    · simp
  · rw [quadraticChar_of_char_gi hχ hx (Or.inr h), h]
    refine ⟨?_, ?_⟩
    · simp [gi]
    · convert h2 using 2 <;> simp [gi]

/-- For `p ≡ 1 (mod 8)` a quartic character is even, so its half sum vanishes. -/
lemma sum_half_char_eq_zero (hp8 : p % 8 = 1) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) :
    ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), χ x = 0 := by
  have hp2 : p ≠ 2 := by omega
  have heven := quartic_apply_neg_one_of_one χ hχ hp8
  have h := sum_eq_two_nsmul_half hp2 (⇑χ) (MulChar.map_zero χ) (fun x => by
    rw [show -x = -1 * x by ring, map_mul, heven, one_mul])
  have hne : χ ≠ 1 := by rintro rfl; rw [orderOf_one] at hχ; norm_num at hχ
  rw [MulChar.sum_eq_zero_of_ne_one hne, two_nsmul] at h
  have : (2 : GaussianInt) * ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), χ x = 0 := by
    rw [two_mul]; exact h.symm
  exact (mul_eq_zero.1 this).resolve_left two_ne_zero

/-- `Re 𝒞 ≡ ∑_H (1 + (x/p)) b(x)` and `Im 𝒞 ≡ ∑_H (1 - (x/p)) b(x) (mod 4)`. -/
lemma bandSum_re_im_modEq (hp8 : p % 8 = 1) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) :
    (bandSum χ).re ≡ ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p),
        (1 + quadraticChar (ZMod p) x) * (band x : ℤ) [ZMOD 4] ∧
      (bandSum χ).im ≡ ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p),
        (1 - quadraticChar (ZMod p) x) * (band x : ℤ) [ZMOD 4] := by
  have h0 := sum_half_char_eq_zero hp8 hχ
  have h0re := congrArg Zsqrtd.re h0
  have h0im := congrArg Zsqrtd.im h0
  rw [re_sum] at h0re
  rw [im_sum] at h0im
  unfold bandSum
  rw [re_sum, im_sum]
  constructor
  · have := Int.ModEq.sum (fun x (_ : x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p)) =>
      (term_modEq hχ x).1)
    rw [sum_add_distrib, h0re] at this
    simpa using this
  · have := Int.ModEq.sum (fun x (_ : x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p)) =>
      (term_modEq hχ x).2)
    rw [sum_add_distrib, h0im] at this
    simpa using this

/-! ### The reflection `3 M₂ = p M₁` and the Legendre-weighted band sum -/

lemma legendre_two_eq_one (hp8 : p % 8 = 1) : legendreSym p 2 = 1 := by
  rw [legendreSym.at_two (by omega), ZMod.χ₈_nat_mod_eight, hp8]; decide

lemma legendre_two_mul (hp8 : p % 8 = 1) (k : ℕ) :
    legendreSym p ((2 * k : ℕ) : ℤ) = legendreSym p k := by
  push_cast
  rw [legendreSym.mul, legendre_two_eq_one hp8, one_mul]

lemma legendre_sub_two_mul (hp8 : p % 8 = 1) {k : ℕ} (hk : 2 * k ≤ p) :
    legendreSym p ((p - 2 * k : ℕ) : ℤ) = legendreSym p k := by
  have h : (((p - 2 * k : ℕ) : ℤ) : ZMod p) = -(((2 * k : ℕ) : ℤ) : ZMod p) := by
    rw [Nat.cast_sub hk]; push_cast; rw [ZMod.natCast_self]; ring
  rw [← legendre_two_mul hp8 k]
  unfold legendreSym
  rw [h, quadraticChar_neg (by omega)]

/-- **The reflection.** With `p = 8q + 1`,
`3 ∑_{v ≤ 4q} (v/p) v² = -p ∑_{2q < k ≤ 4q} (k/p) (p - 4k)`. -/
lemma three_mul_sum_legendre_sq (hp8 : p % 8 = 1) (q : ℕ) (hq : p = 8 * q + 1) :
    3 * ∑ v ∈ range (4 * q + 1), legendreSym p v * (v : ℤ) ^ 2 =
      -(p : ℤ) * ∑ k ∈ range (4 * q + 1),
        (if 2 * q < k then legendreSym p k * ((p : ℤ) - 4 * k) else 0) := by
  set i : ℕ → ℕ := fun k => if k ≤ 2 * q then 2 * k else p - 2 * k with hi
  have hre : ∑ v ∈ range (4 * q + 1), legendreSym p v * (v : ℤ) ^ 2 =
      ∑ k ∈ range (4 * q + 1), legendreSym p (i k : ℕ) * ((i k : ℕ) : ℤ) ^ 2 := by
    symm
    refine Finset.sum_nbij' i (fun n => if n % 2 = 0 then n / 2 else (p - n) / 2)
      ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [mem_range, hi] at hk ⊢; split_ifs <;> omega
    · intro n hn; simp only [mem_range] at hn ⊢; split_ifs <;> omega
    · intro k hk; simp only [mem_range, hi] at hk ⊢; split_ifs <;> omega
    · intro n hn; simp only [mem_range, hi] at hn ⊢; split_ifs <;> omega
    · intro k _; rfl
  have hpt : ∀ k ∈ range (4 * q + 1), legendreSym p (i k : ℕ) * ((i k : ℕ) : ℤ) ^ 2 =
      4 * (legendreSym p k * (k : ℤ) ^ 2) +
        p * (if 2 * q < k then legendreSym p k * ((p : ℤ) - 4 * k) else 0) := by
    intro k hk
    simp only [mem_range] at hk
    by_cases hk2 : k ≤ 2 * q
    · have : ¬ 2 * q < k := by omega
      simp only [hi, hk2, this, ↓reduceIte]
      rw [legendre_two_mul hp8]; push_cast; ring
    · have : 2 * q < k := by omega
      simp only [hi, hk2, this, ↓reduceIte]
      rw [legendre_sub_two_mul hp8 (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have key : ∑ v ∈ range (4 * q + 1), legendreSym p v * (v : ℤ) ^ 2 =
      4 * ∑ v ∈ range (4 * q + 1), legendreSym p v * (v : ℤ) ^ 2 +
        p * ∑ k ∈ range (4 * q + 1),
          (if 2 * q < k then legendreSym p k * ((p : ℤ) - 4 * k) else 0) := by
    conv_lhs => rw [hre]
    rw [sum_congr rfl hpt, sum_add_distrib, ← mul_sum, ← mul_sum]
  linarith

/-- `∑_{2q < k ≤ 4q} (k/p) = -κ`. -/
lemma sum_upper_quarter (hp8 : p % 8 = 1) (q : ℕ) (hq : p = 8 * q + 1) :
    ∑ k ∈ range (4 * q + 1), (if 2 * q < k then legendreSym p k else 0) = -kappa p := by
  have h := sum_legendre_half (p := p) (by omega)
  rw [← sum_filter_add_sum_filter_not _ (fun v => 4 * v < p)] at h
  have e1 : ((range p).filter (fun v => 0 < v ∧ 2 * v < p)).filter (fun v => 4 * v < p) =
      (range p).filter (fun n => 0 < n ∧ 4 * n < p) := by
    ext v; simp only [mem_filter, mem_range]; omega
  have e2 : ((range p).filter (fun v => 0 < v ∧ 2 * v < p)).filter (fun v => ¬ 4 * v < p) =
      (range (4 * q + 1)).filter (fun k => 2 * q < k) := by
    ext v; simp only [mem_filter, mem_range]; omega
  rw [e1, e2] at h
  rw [← sum_filter]
  unfold kappa
  linarith

/-- `κ` is even for `p ≡ 1 (mod 8)`: it is a sum of `(p - 1)/4` signs. -/
lemma kappa_even (hp8 : p % 8 = 1) : ∃ c, kappa p = 2 * c := by
  have hd : (2 : ℤ) ∣ ∑ n ∈ (range p).filter (fun n => 0 < n ∧ 4 * n < p),
      (legendreSym p n + 1) := by
    refine Finset.dvd_sum fun n hn => ?_
    simp only [mem_filter, mem_range] at hn
    have hn0 : ((n : ℤ) : ZMod p) ≠ 0 := by
      rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      intro h; exact absurd (Nat.le_of_dvd hn.2.1 h) (by omega)
    rcases legendreSym.eq_one_or_neg_one p hn0 with h | h <;> rw [h] <;> norm_num
  rw [sum_add_distrib, sum_const, card_first_quarter (by omega)] at hd
  obtain ⟨d, hd⟩ := hd
  refine ⟨d - ((p - 1) / 4 / 2 : ℕ), ?_⟩
  unfold kappa
  have : (((p - 1) / 4 : ℕ) : ℤ) = 2 * ((p - 1) / 4 / 2 : ℕ) := by
    have : (p - 1) / 4 = 2 * ((p - 1) / 4 / 2) := by omega
    exact_mod_cast this
  simp only [nsmul_eq_mul, mul_one] at hd
  linarith

/-- **The Legendre-weighted band sum.** `X = ∑_{x ∈ H} (x/p) b(x) ≡ κ (mod 4)`. -/
lemma sum_legendre_band_modEq (hp8 : p % 8 = 1) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) :
    ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p),
      quadraticChar (ZMod p) x * (band x : ℤ) ≡ kappa p [ZMOD 4] := by
  obtain ⟨q, hq⟩ : ∃ q, p = 8 * q + 1 := ⟨p / 8, by omega⟩
  set H := univ.filter (fun x : ZMod p => 2 * x.val < p) with hH
  set X := ∑ x ∈ H, quadraticChar (ZMod p) x * (band x : ℤ)
  have hR : ∑ x ∈ H, quadraticChar (ZMod p) x * ((x ^ 2).val : ℤ) = 0 :=
    sum_half_legendre_val_sq hp8 hχ
  have hM : ∑ x ∈ H, quadraticChar (ZMod p) x * (x.val : ℤ) ^ 2 = p * X := by
    rw [sum_congr rfl fun x _ => by rw [val_sq_eq x]]
    simp only [mul_add, sum_add_distrib]
    rw [hR, add_zero, mul_sum]
    refine sum_congr rfl fun x _ => by ring
  have hMN : ∑ x ∈ H, quadraticChar (ZMod p) x * (x.val : ℤ) ^ 2 =
      ∑ v ∈ range (4 * q + 1), legendreSym p v * (v : ℤ) ^ 2 := by
    simp only [quadraticChar_eq_legendreSym]
    exact sum_half_val_sq_eq q hq (fun v => legendreSym p (v : ℤ) * (v : ℤ) ^ 2)
  have h3 := three_mul_sum_legendre_sq hp8 q hq
  rw [← hMN, hM] at h3
  set D := ∑ k ∈ range (4 * q + 1),
    (if 2 * q < k then legendreSym p k * ((p : ℤ) - 4 * k) else 0)
  set W := ∑ k ∈ range (4 * q + 1),
    (if 2 * q < k then legendreSym p k * (2 * q - k) else 0)
  have hpq : (p : ℤ) = 8 * q + 1 := by exact_mod_cast hq
  have hD : D = -kappa p + 4 * W := by
    rw [← sum_upper_quarter hp8 q hq, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    split_ifs
    · rw [hpq]; ring
    · ring
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have h3' : 3 * X = -D := by
    have : (p : ℤ) * (3 * X + D) = 0 := by linear_combination h3
    have := (mul_eq_zero.1 this).resolve_left hp0
    linarith
  obtain ⟨c, hc⟩ := kappa_even hp8
  exact Int.modEq_iff_dvd.2 ⟨c - X - W, by linarith⟩

/-! ### The companion law -/

/-- **The companion law at `p ≡ 1 (mod 8)`** (Theorem 4.9). For either quartic character,
`Re 𝒞 ≡ Im 𝒞 ≡ κ = h(-4p)/2 (mod 4)`. -/
theorem companion_one_mod_eight (hp8 : p % 8 = 1) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) :
    (bandSum χ).re ≡ kappa p [ZMOD 4] ∧ (bandSum χ).im ≡ kappa p [ZMOD 4] := by
  obtain ⟨hre, him⟩ := bandSum_re_im_modEq hp8 hχ
  have hB := sum_band_modEq hp8 hχ
  have hX := sum_legendre_band_modEq hp8 hχ
  obtain ⟨c, hc⟩ := kappa_even hp8
  simp only [add_mul, sub_mul, one_mul, sum_add_distrib, sum_sub_distrib] at hre him
  refine ⟨hre.trans ?_, him.trans ?_⟩
  · simpa using hB.add hX
  · refine (hB.sub hX).trans (Int.modEq_iff_dvd.2 ⟨c, by rw [hc]; ring⟩)

end BandParityTower
