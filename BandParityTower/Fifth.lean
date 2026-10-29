module

public import BandParityTower.Inversion
public import BandParityTower.Mod8Defs

@[expose] public section

/-!
# The fifth-interval formula (Theorem 5.9)

For `p ≡ 29 (mod 40)`, with `t_j = ∑_{x < p, x ≡ j (5)} (x/p)`:

* `5p B_{1,θ_p} = 5p ((t_0 + t_4) - i t_2)` (`fifth_theta_re`, `fifth_theta_im`);
* `t_3 = t_1` (negation) and `t_1 = 2R_5 - v` (the substitution `x = 5n - p`);
* `M_H(5) = Q - 2R_5`, by the sign identity `s(u) s(5u) = -1` exactly on the fifths `1, 3`;
* `5 ∈ H` iff `R_5` is even, by comparing `∏_{u ∈ H} s(u) s(5u)` with `(-1)^{R_5}`.
-/

namespace BandParityTower
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Legendre symbol facts -/

lemma fifth_leg_congr {n m : ℕ} (h : (n : ZMod p) = (m : ZMod p)) :
    legendreSym p (n : ℤ) = legendreSym p (m : ℤ) := by
  simp only [legendreSym, Int.cast_natCast, h]

lemma fifth_leg_sum_zero (hp2 : p ≠ 2) : ∑ x ∈ range p, legendreSym p (x : ℤ) = 0 := by
  have h := quadraticChar_sum_zero (F := ZMod p) (ringChar_ne_two hp2)
  simp only [quadraticChar_eq_legendreSym] at h
  have h2 := sum_filter_val (p := p) (fun _ => True) (fun v => legendreSym p (v : ℤ))
  rw [Finset.filter_true, Finset.filter_true] at h2
  rw [← h2]; exact h

lemma fifth_leg_five (hp40 : p % 40 = 29) : legendreSym p 5 = 1 := by
  have h2 : ((2 : ℤ) : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := legendreSym.quadratic_reciprocity_one_mod_four (p := p) (q := 5) (by omega)
    (by norm_num)
  push_cast at h
  rw [← h, legendreSym.mod]
  have : (p : ℤ) % ((5 : ℕ) : ℤ) = 2 ^ 2 := by push_cast; omega
  rw [this]
  exact legendreSym.sq_one' 5 h2

/-! ### The theta sum -/

omit hp in
lemma fifth_sum_range_five (f : ℕ → GaussianInt) :
    ∑ n ∈ range (5 * p), f n = ∑ x ∈ range p,
      (f x + f (p + x) + f (p + p + x) + f (p + p + p + x) + f (p + p + p + p + x)) := by
  rw [show 5 * p = p + p + p + p + p by ring]
  simp only [sum_range_add, ← sum_add_distrib]

/-- Real coefficient `Re c(j)`. -/
def fifthCr (j : ℕ) : ℤ := if j = 0 ∨ j = 4 then 3 else -2

/-- Imaginary coefficient `Im c(j)`. -/
def fifthCi (j : ℕ) : ℤ := if j = 2 then -4 else 1

lemma fifth_theta_term (hp40 : p % 40 = 29) (f : ℕ → GaussianInt)
    (hf : ∀ n, f n = ((legendreSym p n : ℤ) : GaussianInt) * xi5 n * (n : GaussianInt)) (x : ℕ) :
    f x + f (p + x) + f (p + p + x) + f (p + p + p + x) + f (p + p + p + p + x) =
      ((legendreSym p x * p * fifthCr (x % 5) : ℤ) : GaussianInt) +
        gi * ((legendreSym p x * p * fifthCi (x % 5) : ℤ) : GaussianInt) := by
  simp only [hf]
  rw [fifth_leg_congr (n := p + x) (m := x) (by simp),
    fifth_leg_congr (n := p + p + x) (m := x) (by simp),
    fifth_leg_congr (n := p + p + p + x) (m := x) (by simp),
    fifth_leg_congr (n := p + p + p + p + x) (m := x) (by simp)]
  rcases (by omega : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4) with
    h | h | h | h | h
  · have e1 : (p + x) % 5 = 4 := by omega
    have e2 : (p + p + x) % 5 = 3 := by omega
    have e3 : (p + p + p + x) % 5 = 2 := by omega
    have e4 : (p + p + p + p + x) % 5 = 1 := by omega
    simp only [xi5, fifthCr, fifthCi, h, e1, e2, e3, e4]
    norm_num
    ring
  · have e1 : (p + x) % 5 = 0 := by omega
    have e2 : (p + p + x) % 5 = 4 := by omega
    have e3 : (p + p + p + x) % 5 = 3 := by omega
    have e4 : (p + p + p + p + x) % 5 = 2 := by omega
    simp only [xi5, fifthCr, fifthCi, h, e1, e2, e3, e4]
    norm_num
    ring
  · have e1 : (p + x) % 5 = 1 := by omega
    have e2 : (p + p + x) % 5 = 0 := by omega
    have e3 : (p + p + p + x) % 5 = 4 := by omega
    have e4 : (p + p + p + p + x) % 5 = 3 := by omega
    simp only [xi5, fifthCr, fifthCi, h, e1, e2, e3, e4]
    norm_num
    ring
  · have e1 : (p + x) % 5 = 2 := by omega
    have e2 : (p + p + x) % 5 = 1 := by omega
    have e3 : (p + p + p + x) % 5 = 0 := by omega
    have e4 : (p + p + p + p + x) % 5 = 4 := by omega
    simp only [xi5, fifthCr, fifthCi, h, e1, e2, e3, e4]
    norm_num
    ring
  · have e1 : (p + x) % 5 = 3 := by omega
    have e2 : (p + p + x) % 5 = 2 := by omega
    have e3 : (p + p + p + x) % 5 = 1 := by omega
    have e4 : (p + p + p + p + x) % 5 = 0 := by omega
    simp only [xi5, fifthCr, fifthCi, h, e1, e2, e3, e4]
    norm_num
    ring

lemma fifth_theta_eq (hp40 : p % 40 = 29) :
    thetaSum p = ((∑ x ∈ range p, legendreSym p x * p * fifthCr (x % 5) : ℤ) : GaussianInt) +
      gi * ((∑ x ∈ range p, legendreSym p x * p * fifthCi (x % 5) : ℤ) : GaussianInt) := by
  unfold thetaSum
  rw [fifth_sum_range_five, sum_congr rfl (fun x _ => fifth_theta_term hp40 _ (fun n => rfl) x),
    sum_add_distrib, ← mul_sum]
  push_cast
  rfl

/-- `t_{0,4} = ∑_{x < p, x ≡ 0, 4 (5)} (x/p)`. -/
lemma fifth_sum_cr (hp40 : p % 40 = 29) :
    ∑ x ∈ range p, legendreSym p x * p * fifthCr (x % 5) =
      5 * p * ∑ x ∈ (range p).filter (fun x => x % 5 = 0 ∨ x % 5 = 4), legendreSym p x := by
  have h : ∀ x ∈ range p, legendreSym p x * p * fifthCr (x % 5) =
      p * (5 * (if x % 5 = 0 ∨ x % 5 = 4 then legendreSym p x else 0) - 2 * legendreSym p x) := by
    intro x _
    unfold fifthCr
    split_ifs <;> ring
  rw [sum_congr rfl h, ← mul_sum, sum_sub_distrib, ← mul_sum, ← mul_sum, ← sum_filter,
    fifth_leg_sum_zero (by omega)]
  ring

lemma fifth_sum_ci (hp40 : p % 40 = 29) :
    ∑ x ∈ range p, legendreSym p x * p * fifthCi (x % 5) =
      -(5 * p * ∑ x ∈ (range p).filter (fun x => x % 5 = 2), legendreSym p x) := by
  have h : ∀ x ∈ range p, legendreSym p x * p * fifthCi (x % 5) =
      p * (legendreSym p x - 5 * (if x % 5 = 2 then legendreSym p x else 0)) := by
    intro x _
    unfold fifthCi
    split_ifs <;> ring
  rw [sum_congr rfl h, ← mul_sum, sum_sub_distrib, ← mul_sum, ← sum_filter,
    fifth_leg_sum_zero (by omega)]
  ring

lemma fifth_theta_re (hp40 : p % 40 = 29) :
    (thetaSum p).re =
      5 * p * ∑ x ∈ (range p).filter (fun x => x % 5 = 0 ∨ x % 5 = 4), legendreSym p x := by
  rw [fifth_theta_eq hp40, re_add_gi_mul, fifth_sum_cr hp40]

lemma fifth_theta_im (hp40 : p % 40 = 29) :
    (thetaSum p).im = -(5 * p * ∑ x ∈ (range p).filter (fun x => x % 5 = 2), legendreSym p x) := by
  rw [fifth_theta_eq hp40, im_add_gi_mul, fifth_sum_ci hp40]

/-! ### The classes `t_j` -/

lemma fifth_partition :
    ∑ x ∈ range p, legendreSym p (x : ℤ) =
      ∑ x ∈ (range p).filter (fun x => x % 5 = 0 ∨ x % 5 = 4), legendreSym p x +
      ∑ x ∈ (range p).filter (fun x => x % 5 = 2), legendreSym p x +
      ∑ x ∈ (range p).filter (fun x => x % 5 = 1), legendreSym p x +
      ∑ x ∈ (range p).filter (fun x => x % 5 = 3), legendreSym p x := by
  simp only [sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rcases (by omega : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4) with
    h | h | h | h | h <;> simp [h]

lemma fifth_t3 (hp40 : p % 40 = 29) :
    ∑ x ∈ (range p).filter (fun x => x % 5 = 3), legendreSym p (x : ℤ) =
      ∑ x ∈ (range p).filter (fun x => x % 5 = 1), legendreSym p x := by
  refine sum_nbij' (fun x => p - x) (fun x => p - x) ?_ ?_ ?_ ?_ ?_
  · intro x hx; simp only [mem_filter, mem_range] at hx ⊢; omega
  · intro x hx; simp only [mem_filter, mem_range] at hx ⊢; omega
  · intro x hx; simp only [mem_filter, mem_range] at hx; omega
  · intro x hx; simp only [mem_filter, mem_range] at hx; omega
  · intro x hx
    simp only [mem_filter, mem_range] at hx
    simp only [legendreSym]
    rw [Nat.cast_sub hx.1.le]
    push_cast
    rw [ZMod.natCast_self, zero_sub, quadraticChar_neg (by omega)]

/-! ### The second fifth -/

lemma fifth_natCast_ne_zero {n : ℕ} (h0 : 0 < n) (hn : n < p) : (n : ZMod p) ≠ 0 := by
  intro h
  have := ZMod.val_natCast_of_lt hn
  rw [h, ZMod.val_zero] at this
  omega

/-- The substitution `x = 5n - p` carries the second fifth onto `x ≡ 1 (mod 5)`, and `(5/p) = 1`. -/
lemma fifth_t1 (hp40 : p % 40 = 29) :
    ∑ x ∈ (range p).filter (fun x => x % 5 = 1), legendreSym p (x : ℤ) =
      ∑ n ∈ (range p).filter (fun n => p < 5 * n ∧ 5 * n < 2 * p), legendreSym p n := by
  refine sum_nbij' (fun x => (x + p) / 5) (fun n => 5 * n - p) ?_ ?_ ?_ ?_ ?_
  · intro x hx; simp only [mem_filter, mem_range, coe_filter, Set.mem_ofPred_eq] at hx ⊢; omega
  · intro x hx; simp only [mem_filter, mem_range, coe_filter, Set.mem_ofPred_eq] at hx ⊢; omega
  · intro x hx; simp only [mem_filter, mem_range, coe_filter, Set.mem_ofPred_eq] at hx; omega
  · intro x hx; simp only [mem_filter, mem_range, coe_filter, Set.mem_ofPred_eq] at hx; omega
  · intro x hx
    simp only [mem_filter, mem_range] at hx
    have hx5 : x + p = 5 * ((x + p) / 5) := by omega
    have hc : (x : ZMod p) = ((5 * ((x + p) / 5) : ℕ) : ZMod p) := by
      rw [← hx5]; push_cast; simp
    rw [fifth_leg_congr hc]
    push_cast
    rw [legendreSym.mul, fifth_leg_five hp40, one_mul]

lemma fifth_J_eq (hp40 : p % 40 = 29) :
    (range p).filter (fun n => p < 5 * n ∧ 5 * n < 2 * p) =
      Ico ((p + 1) / 5) (2 * ((p + 1) / 5)) := by
  ext n; simp only [mem_filter, mem_range, mem_Ico]; omega

lemma fifth_sum_J (hp40 : p % 40 = 29) :
    ∑ n ∈ (range p).filter (fun n => p < 5 * n ∧ 5 * n < 2 * p), legendreSym p (n : ℤ) =
      2 * (fifthCount p : ℤ) - ((p + 1) / 5 : ℕ) := by
  set J := (range p).filter (fun n => p < 5 * n ∧ 5 * n < 2 * p) with hJ
  have h : ∀ n ∈ J, legendreSym p (n : ℤ) =
      2 * (if legendreSym p (n : ℤ) = 1 then 1 else 0) - 1 := by
    intro n hn
    simp only [hJ, mem_filter, mem_range] at hn
    have hne : ((n : ℤ) : ZMod p) ≠ 0 := by
      rw [Int.cast_natCast]; exact fifth_natCast_ne_zero (by omega) hn.1
    rcases legendreSym.eq_one_or_neg_one p hne with h1 | h1 <;> rw [h1] <;> norm_num
  have hcount : fifthCount p = (J.filter fun n => legendreSym p (n : ℤ) = 1).card := by
    unfold fifthCount; rw [hJ, filter_filter]; congr 1; ext n; simp only [mem_filter]; tauto
  have hcard : J.card = (p + 1) / 5 := by
    rw [hJ, fifth_J_eq hp40, Nat.card_Ico]; omega
  rw [sum_congr rfl h, sum_sub_distrib, ← mul_sum, sum_boole, sum_const, hcount, hcard]
  simp

/-! ### The multiplier `5` on `H` -/

lemma fifth_val5 (hp40 : p % 40 = 29) : (5 : ZMod p).val = 5 := by
  rw [show (5 : ZMod p) = ((5 : ℕ) : ZMod p) by norm_cast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (by omega)]

omit hp in
lemma fifth_neg_one_pow (n : ℕ) : (-1 : ℤ) ^ n = if n % 2 = 0 then 1 else -1 := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, ite_eq_left (Nat.even_iff.1 h)]
  · rw [h.neg_one_pow, ite_eq_right (by rw [Nat.odd_iff] at h; omega)]

/-- The fifths `1` and `3`: `⌊5⟨u⟩/p⌋` odd. -/
def fifthOdd (p : ℕ) (u : ZMod p) : Prop :=
  (p < 5 * u.val ∧ 5 * u.val < 2 * p) ∨ (3 * p < 5 * u.val ∧ 5 * u.val < 4 * p)

instance (u : ZMod p) : Decidable (fifthOdd p u) := by unfold fifthOdd; infer_instance

/-- **The sign identity.** `s(u) s(5u) = (-1)^{⌊5⟨u⟩/p⌋}`, which is `-1` exactly on the
fifths `1` and `3`. -/
lemma fifth_sign (hp40 : p % 40 = 29) (u : ZMod p) :
    parSign u * parSign (5 * u) = if fifthOdd p u then -1 else 1 := by
  unfold parSign fifthOdd
  rw [ZMod.val_mul, fifth_val5 hp40, ← pow_add, fifth_neg_one_pow]
  have hv := ZMod.val_lt u
  have hp0 := hp.out.pos
  have hd := Nat.div_add_mod (5 * u.val) p
  have hr := Nat.mod_lt (5 * u.val) hp0
  have hq : 5 * u.val / p < 5 := (Nat.div_lt_iff_lt_mul hp0).2 (by omega)
  generalize 5 * u.val / p = q at hd hq
  generalize 5 * u.val % p = r at hd hr ⊢
  interval_cases q <;> split_ifs <;> omega

lemma fifth_multCorr (hp40 : p % 40 = 29) :
    multCorr (5 : ZMod p) = Q p - 2 * ((Ha p).filter (fifthOdd p)).card := by
  have hc := filter_card_add_filter_neg_card_eq_card (s := Ha p) (fifthOdd p)
  rw [card_Ha, oddPart_five (by omega)] at hc
  unfold multCorr Q
  rw [sum_congr rfl (fun u _ => fifth_sign hp40 u), sum_ite, sum_const, sum_const]
  simp only [nsmul_eq_mul]
  push_cast
  omega

end BandParityTower
