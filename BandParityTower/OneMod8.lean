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
  simp [Finset.filter_ne']

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

end BandParityTower
