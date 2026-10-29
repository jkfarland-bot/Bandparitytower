module

public import BandParityTower.Tower

@[expose] public section

/-!
# Quartic characters and power residues

For a quartic character `χ` modulo `p` with values in `ℤ[i]`:

* `char_eq_one_iff`: `χ(n) = 1` exactly when `n` is a nonzero fourth power;
* `legendre_eq_sq`: `(n/p) = χ(n)²` for `n ≠ 0`;
* `indicator_fourth`: `4 [n is a fourth power] = 1 + (n/p) + 2 Re χ(n)` for `n ≠ 0`;
* `twoVal_eq_of`: `a = j` when `p - 1 = 2^j q` with `q` odd.
-/

namespace BandParityTower

open Finset

lemma twoVal_eq_of {n j q : ℕ} (h : n - 1 = 2 ^ j * q) (hq : Odd q) : twoVal n = j := by
  unfold twoVal
  rw [h, padicValNat.mul (by positivity) hq.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]),
    add_zero]

lemma re_sum {ι : Type*} (s : Finset ι) (f : ι → GaussianInt) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [sum_cons, sum_cons, Zsqrtd.re_add, ih]

lemma im_sum {ι : Type*} (s : Finset ι) (f : ι → GaussianInt) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [sum_cons, sum_cons, Zsqrtd.im_add, ih]

lemma gi_pow_eq_one_iff {u : GaussianInt} (hu : u = gi ∨ u = -gi) (j : ℕ) :
    u ^ j = 1 ↔ 4 ∣ j := by
  have h4 : u ^ 4 = 1 := by rcases hu with rfl | rfl <;> decide
  have key : u ^ j = u ^ (j % 4) := by
    conv_lhs => rw [← Nat.mod_add_div j 4, pow_add, pow_mul, h4, one_pow, mul_one]
  rw [key, Nat.dvd_iff_mod_eq_zero]
  have hlt := Nat.mod_lt j (show 0 < 4 by norm_num)
  interval_cases (j % 4) <;> rcases hu with rfl | rfl <;> decide

variable {p : ℕ} [hp : Fact p.Prime]

section Quartic

variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

/-- `χ(n) = 1` exactly when `n` is a nonzero fourth power. -/
theorem char_eq_one_iff {n : ZMod p} (hn : n ≠ 0) : χ n = 1 ↔ ∃ y : ZMod p, y ^ 4 = n := by
  constructor
  · intro h
    obtain ⟨g, -, hg⟩ := exists_generator (p := p)
    obtain ⟨j, hj⟩ := hg (Units.mk0 n hn)
    have hnj : n = (g : ZMod p) ^ j := by
      have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hj
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
      exact this.symm
    rw [hnj, map_pow, gi_pow_eq_one_iff (quartic_apply_generator χ hχ hg)] at h
    obtain ⟨q, rfl⟩ := h
    exact ⟨(g : ZMod p) ^ q, by rw [hnj, ← pow_mul, mul_comm]⟩
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by rintro rfl; exact hn (by simp)
    rw [map_pow]
    rcases quartic_values χ hχ hy with h | h | h | h <;> rw [h] <;> decide

/-- `(n/p) = χ(n)²` for `n ≠ 0`. -/
theorem quadraticChar_eq_sq {n : ZMod p} (hn : n ≠ 0) :
    ((quadraticChar (ZMod p) n : ℤ) : GaussianInt) = χ n ^ 2 := by
  rcases quartic_values χ hχ hn with h | h | h | h
  · rw [quadraticChar_of_char_one hχ hn (Or.inl h), h]; simp
  · rw [quadraticChar_of_char_gi hχ hn (Or.inl h), h, gi_sq]; simp
  · rw [quadraticChar_of_char_one hχ hn (Or.inr h), h]; simp
  · rw [quadraticChar_of_char_gi hχ hn (Or.inr h), h, neg_sq, gi_sq]; simp

/-- `4 [n is a fourth power] = 1 + (n/p) + 2 Re χ(n)` for `n ≠ 0`. -/
theorem indicator_fourth {n : ZMod p} (hn : n ≠ 0) :
    (4 * (if ∃ y : ZMod p, y ^ 4 = n then 1 else 0) : ℤ) =
      1 + quadraticChar (ZMod p) n + 2 * (χ n).re := by
  simp only [← char_eq_one_iff hχ hn]
  rcases quartic_values χ hχ hn with h | h | h | h
  · rw [quadraticChar_of_char_one hχ hn (Or.inl h), h]; simp
  · rw [quadraticChar_of_char_gi hχ hn (Or.inl h), h, ite_eq_right gi_ne_one]; simp [gi]
  · rw [quadraticChar_of_char_one hχ hn (Or.inr h), h]; simp [show (-1 : GaussianInt) ≠ 1 by decide]
  · rw [quadraticChar_of_char_gi hχ hn (Or.inr h), h, ite_eq_right (show -gi ≠ 1 by decide)]; simp [gi]

end Quartic

/-! ### The level `a = 3` -/

omit hp in
lemma card_first_quarter (hp4 : p % 4 = 1) :
    ((range p).filter fun n => 0 < n ∧ 4 * n < p).card = (p - 1) / 4 := by
  have : (range p).filter (fun n => 0 < n ∧ 4 * n < p) = Ioc 0 ((p - 1) / 4) := by
    ext n; simp only [mem_filter, mem_range, mem_Ioc]; omega
  rw [this, Nat.card_Ioc]; omega

/-- **The imaginary law at level three** (Corollary 4.6). For `p ≡ 9 (mod 16)` and either quartic
character `χ`, with `Ω = ∑_{0 < n < p/4} χ(n)`: `2 (2N_3 - m) = κ + 2 Re Ω`, and hence
`2 e_3 ≡ κ + 2 Re Ω (mod 8)`, that is, `e_3 ≡ (κ + 2 Re Ω)/2 (mod 4)`. -/
theorem elaw_three (hp16 : p % 16 = 9) {χ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) :
    2 * (2 * (Na p : ℤ) - oddPart p) =
        kappa p + 2 * (∑ n ∈ (range p).filter (fun n => 0 < n ∧ 4 * n < p), χ (n : ZMod p)).re ∧
      2 * eTower p ≡
        kappa p + 2 * (∑ n ∈ (range p).filter (fun n => 0 < n ∧ 4 * n < p), χ (n : ZMod p)).re
        [ZMOD 8] := by
  have hp4 : p % 4 = 1 := by omega
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have ha : twoVal p = 3 := twoVal_eq_of (q := (p - 1) / 8)
    (by norm_num; omega) (by rw [Nat.odd_iff]; omega)
  have hm : (oddPart p : ℤ) = ((p - 1) / 8 : ℕ) := by
    unfold oddPart; rw [ha]; norm_num
  set S := (range p).filter (fun n => 0 < n ∧ 4 * n < p)
  have hS0 : ∀ n ∈ S, ((n : ℕ) : ZMod p) ≠ 0 := by
    intro n hn
    simp only [S, mem_filter, mem_range] at hn
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h; exact absurd (Nat.le_of_dvd hn.2.1 h) (by omega)
  have hN : 4 * (Na p : ℤ) = ((p - 1) / 4 : ℕ) + kappa p + 2 * (∑ n ∈ S, χ (n : ZMod p)).re := by
    have hNa : (Na p : ℤ) = ∑ n ∈ S, (if ∃ y : ZMod p, y ^ 4 = (n : ZMod p) then 1 else 0) := by
      unfold Na powResCount
      rw [ha, sum_boole]
      simp only [Nat.cast_inj, filter_filter, S]
      congr 1
      ext n; simp only [mem_filter, mem_range]; norm_num [and_assoc]
    rw [hNa, mul_sum, sum_congr rfl fun n hn => indicator_fourth hχ (hS0 n hn), sum_add_distrib,
      sum_add_distrib, sum_const, ← mul_sum, ← re_sum]
    rw [card_first_quarter hp4]
    unfold kappa
    simp only [nsmul_eq_mul, mul_one, S]
    congr 2
    refine sum_congr rfl fun n _ => ?_
    unfold legendreSym; simp
  have hlaw : 2 * (2 * (Na p : ℤ) - oddPart p) =
      kappa p + 2 * (∑ n ∈ S, χ (n : ZMod p)).re := by
    rw [hm]
    have : (((p - 1) / 8 : ℕ) : ℤ) * 2 = ((p - 1) / 4 : ℕ) := by
      have : (p - 1) / 8 * 2 = (p - 1) / 4 := by omega
      exact_mod_cast this
    linarith
  refine ⟨hlaw, ?_⟩
  rw [← hlaw]
  have : 2 * eTower p ≡ 2 * (2 * (Na p : ℤ) - oddPart p) [ZMOD 2 * 4] :=
    (eTower_modEq hp4).mul_left'
  exact this

end BandParityTower
