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
  · intro x hx; simp only [mem_filter, mem_range] at hx ⊢; omega
  · intro x hx; simp only [mem_filter, mem_range] at hx ⊢; omega
  · intro x hx; simp only [mem_filter, mem_range] at hx; omega
  · intro x hx; simp only [mem_filter, mem_range] at hx; omega
  · intro x hx
    simp only [mem_filter, mem_range] at hx
    have hx5 : x + p = 5 * ((x + p) / 5) := by omega
    have hc : (x : ZMod p) = ((5 * ((x + p) / 5) : ℕ) : ZMod p) := by
      rw [← hx5]; push_cast; simp
    rw [fifth_leg_congr hc]
    push_cast
    rw [legendreSym.mul, fifth_leg_five hp40, one_mul]

omit hp in
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
  have hcount : fifthCount p = (J.filter fun n : ℕ => legendreSym p (n : ℤ) = 1).card := by
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
  have h : ∀ u ∈ Ha p, parSign u * parSign (5 * u) =
      1 - 2 * (if fifthOdd p u then (1 : ℤ) else 0) := by
    intro u _; rw [fifth_sign hp40 u]; split_ifs <;> ring
  unfold multCorr Q
  rw [sum_congr rfl h, sum_sub_distrib, ← mul_sum, sum_boole, sum_const, card_Ha,
    oddPart_five (by omega)]
  simp

/-! ### Counting the fourth powers in the fifths `1` and `3` -/

lemma fifth_leg_one_iff (hp40 : p % 40 = 29) {x : ZMod p} (hx : x ≠ 0) :
    legendreSym p (x.val : ℤ) = 1 ↔ (x ∈ Ha p ∨ -x ∈ Ha p) := by
  have hcast : (((x.val : ℕ) : ℤ) : ZMod p) = x := by simp
  rw [pm_Ha_iff (by omega), legendreSym.eq_one_iff p (by rw [hcast]; exact hx), hcast,
    ZMod.euler_criterion p hx, oddPart_five (by omega),
    show 2 * ((p - 1) / 4) = p / 2 by omega]

lemma fifth_five_ne_zero (hp40 : p % 40 = 29) : (5 : ZMod p) ≠ 0 := by
  intro h; have := fifth_val5 hp40; rw [h, ZMod.val_zero] at this; omega

lemma fifth_five_pm (hp40 : p % 40 = 29) : (5 : ZMod p) ∈ Ha p ∨ -(5 : ZMod p) ∈ Ha p := by
  rw [← fifth_leg_one_iff hp40 (fifth_five_ne_zero hp40), fifth_val5 hp40]
  exact_mod_cast fifth_leg_five hp40

lemma fifth_val_neg {x : ZMod p} (hx : x ≠ 0) : (-x).val = p - x.val := val_neg_of_ne_zero hx

lemma fifth_count_H (hp40 : p % 40 = 29) :
    ((Ha p).filter (fifthOdd p)).card = fifthCount p := by
  have hp2 : p ≠ 2 := by omega
  -- the two fifths
  have hsplit : (Ha p).filter (fifthOdd p) =
      (Ha p).filter (fun u => p < 5 * u.val ∧ 5 * u.val < 2 * p) ∪
        (Ha p).filter (fun u => 3 * p < 5 * u.val ∧ 5 * u.val < 4 * p) := by
    rw [← filter_or]; rfl
  have hdisj : Disjoint ((Ha p).filter (fun u => p < 5 * u.val ∧ 5 * u.val < 2 * p))
      ((Ha p).filter (fun u => 3 * p < 5 * u.val ∧ 5 * u.val < 4 * p)) := by
    rw [disjoint_filter]; intro u _ h1 h2; omega
  -- negation carries the fourth fifth onto the second
  have hneg : ((Ha p).filter (fun u => 3 * p < 5 * u.val ∧ 5 * u.val < 4 * p)).card =
      (univ.filter (fun x : ZMod p => (p < 5 * x.val ∧ 5 * x.val < 2 * p) ∧ -x ∈ Ha p)).card := by
    refine card_nbij' (fun u => -u) (fun x => -x) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
      have hu0 := ne_zero_of_mem_Ha hu.1
      have hv := ZMod.val_lt u
      rw [neg_neg, fifth_val_neg hu0]
      exact ⟨by omega, hu.1⟩
    · intro x hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      have hx0 : x ≠ 0 := by rintro rfl; simp at hx
      have hv := ZMod.val_lt x
      rw [fifth_val_neg hx0]
      exact ⟨hx.2, by omega⟩
    · intro u _; simp
    · intro x _; simp
  have hpos : ((Ha p).filter (fun u => p < 5 * u.val ∧ 5 * u.val < 2 * p)) =
      univ.filter (fun x : ZMod p => (p < 5 * x.val ∧ 5 * x.val < 2 * p) ∧ x ∈ Ha p) := by
    ext x; simp only [mem_filter, mem_univ, true_and]; tauto
  -- the quadratic residues in the second fifth
  have hres : univ.filter (fun x : ZMod p => (p < 5 * x.val ∧ 5 * x.val < 2 * p) ∧
      (x ∈ Ha p ∨ -x ∈ Ha p)) =
      univ.filter (fun x : ZMod p => (p < 5 * x.val ∧ 5 * x.val < 2 * p) ∧ x ∈ Ha p) ∪
      univ.filter (fun x : ZMod p => (p < 5 * x.val ∧ 5 * x.val < 2 * p) ∧ -x ∈ Ha p) := by
    rw [← filter_or]; ext x; simp only [mem_filter, mem_univ, true_and]; tauto
  have hdisj' : Disjoint
      (univ.filter (fun x : ZMod p => (p < 5 * x.val ∧ 5 * x.val < 2 * p) ∧ x ∈ Ha p))
      (univ.filter (fun x : ZMod p => (p < 5 * x.val ∧ 5 * x.val < 2 * p) ∧ -x ∈ Ha p)) := by
    rw [disjoint_filter]
    intro x _ h1 h2
    have := neg_not_mem_coset hp2 (one_ne_zero (α := ZMod p))
      (show x ∈ cosetOf 1 (Ha p) by rw [cosetOf_one]; exact h1.2)
    rw [cosetOf_one] at this
    exact this h2.2
  have hfc : fifthCount p = (univ.filter (fun x : ZMod p => (p < 5 * x.val ∧ 5 * x.val < 2 * p) ∧
      (x ∈ Ha p ∨ -x ∈ Ha p))).card := by
    have h := sum_filter_val (p := p)
      (fun n => p < 5 * n ∧ 5 * n < 2 * p ∧ legendreSym p (n : ℤ) = 1) (fun _ => (1 : ℕ))
    simp only [sum_const, smul_eq_mul, mul_one] at h
    unfold fifthCount
    rw [← h]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hx0 : x ≠ 0 := by rintro rfl; simp at h1
      exact ⟨⟨h1, h2⟩, (fifth_leg_one_iff hp40 hx0).1 h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hx0 : x ≠ 0 := by rintro rfl; simp at h1
      exact ⟨h1, h2, (fifth_leg_one_iff hp40 hx0).2 h3⟩
  rw [hsplit, card_union_of_disjoint hdisj, hneg, hpos, hfc, hres, card_union_of_disjoint hdisj']

/-! ### Parity: `5 ∈ H` iff `R_5` is even -/

lemma fifth_prod_mul_mem {c : ZMod p} (hc : c ∈ Ha p) :
    ∏ u ∈ Ha p, parSign (c * u) = ∏ u ∈ Ha p, parSign u := by
  have hc0 := ne_zero_of_mem_Ha hc
  rw [← prod_image (f := parSign) (s := Ha p) (g := (c * ·))
    (fun x _ y _ h => mul_left_cancel₀ hc0 h)]
  rw [show (Ha p).image (c * ·) = cosetOf c (Ha p) from rfl, cosetOf_eq_of_mem hc]

lemma fifth_prod (hp40 : p % 40 = 29) :
    ∏ u ∈ Ha p, (parSign u * parSign (5 * u)) = if (5 : ZMod p) ∈ Ha p then 1 else -1 := by
  have hp2 : p ≠ 2 := by omega
  have hsq : (∏ u ∈ Ha p, parSign u) * ∏ u ∈ Ha p, parSign u = 1 := by
    rw [← prod_mul_distrib]; simp [parSign_mul_self]
  rw [prod_mul_distrib]
  split_ifs with h5
  · rw [fifth_prod_mul_mem h5, hsq]
  · have h5' : -(5 : ZMod p) ∈ Ha p := (fifth_five_pm hp40).resolve_left h5
    have e : ∀ u ∈ Ha p, parSign (5 * u) = -parSign (-5 * u) := by
      intro u hu
      have hne : (-5 : ZMod p) * u ≠ 0 :=
        mul_ne_zero (neg_ne_zero.2 (fifth_five_ne_zero hp40)) (ne_zero_of_mem_Ha hu)
      rw [show (5 : ZMod p) * u = -(-5 * u) by ring, parSign_neg hp2 hne]
    rw [prod_congr rfl e, prod_neg, card_Ha, (oddPart_odd prime_two_le).neg_one_pow,
      show (-5 : ZMod p) = -(5 : ZMod p) by ring, fifth_prod_mul_mem h5', neg_one_mul,
      mul_neg, hsq]

lemma fifth_mem_iff_even (hp40 : p % 40 = 29) :
    (5 : ZMod p) ∈ Ha p ↔ Even ((Ha p).filter (fifthOdd p)).card := by
  have h := fifth_prod hp40
  rw [prod_congr rfl (fun u _ => fifth_sign hp40 u), prod_ite, prod_const, prod_const_one,
    mul_one] at h
  have hne : (-1 : ℤ) ≠ 1 := by norm_num
  constructor
  · intro h5
    rw [ite_eq_left h5] at h
    exact (neg_one_pow_eq_one_iff_even hne).1 h
  · intro he
    by_contra h5
    rw [ite_eq_right h5, (neg_one_pow_eq_one_iff_even hne).2 he] at h
    exact hne h.symm

/-! ### The defect of `5` -/

lemma fifth_defect (hp40 : p % 40 = 29) : defect (5 : ZMod p) = 1 := by
  have hinv : (5 : ZMod p)⁻¹ = (((p + 1) / 5 : ℕ) : ZMod p) := by
    refine inv_eq_of_mul_eq_one_right ?_
    have h5 : 5 * ((p + 1) / 5) = p + 1 := by omega
    have h := congrArg (Nat.cast : ℕ → ZMod p) h5
    push_cast at h
    rw [h, ZMod.natCast_self, zero_add]
  have hodd : ¬ Odd ((p + 1) / 5) := by rw [Nat.not_odd_iff_even, Nat.even_iff]; omega
  unfold defect oddInd
  rw [hinv, ZMod.val_natCast_of_lt (by omega), fifth_val5 hp40,
    ite_eq_left (by decide : Odd 5), ite_eq_right hodd]
  norm_num

/-! ### The fifth-interval formula -/

/-- **The fifth-interval formula** (Theorem 5.9). Let `p ≡ 29 (mod 40)`, `v = (p + 1)/5`,
`R_5(p)` the number of quadratic residues in `(p/5, 2p/5)`, `θ_p = (·/p) ξ` with `ξ` the quartic
character modulo `5` with `ξ(2) = i`, and `B_{1,θ_p} = R + i I`. Then `R`, `I` are integers,
`R_5 = (2v + I - R)/4`, `M_H(5) = Q - v + (R - I)/2`; `5 ∈ H` iff `R - I ≡ 2v (mod 8)`; and
then the pair `{5, 5⁻¹}` contributes `4` modulo `8` to the sum of Lemma 5.7 iff
`R - I ≡ 2v - 8 (mod 16)`. -/
theorem fifth_interval (hp40 : p % 40 = 29) :
    ((5 * p : ℕ) : ℤ) ∣ (thetaSum p).re ∧ ((5 * p : ℕ) : ℤ) ∣ (thetaSum p).im ∧
      4 * (fifthCount p : ℤ) = 2 * ((p + 1) / 5 : ℕ) + (thetaSum p).im / (5 * p : ℕ) -
        (thetaSum p).re / (5 * p : ℕ) ∧
      2 * multCorr (5 : ZMod p) = 2 * Q p - 2 * ((p + 1) / 5 : ℕ) +
        (thetaSum p).re / (5 * p : ℕ) - (thetaSum p).im / (5 * p : ℕ) ∧
      ((5 : ZMod p) ∈ Ha p ↔ (thetaSum p).re / (5 * p : ℕ) - (thetaSum p).im / (5 * p : ℕ) ≡
        2 * ((p + 1) / 5 : ℕ) [ZMOD 8]) ∧
      ((5 : ZMod p) ∈ Ha p →
        (defect (5 : ZMod p) * (multCorr (5 : ZMod p) - Q p) ≡ 4 [ZMOD 8] ↔
          (thetaSum p).re / (5 * p : ℕ) - (thetaSum p).im / (5 * p : ℕ) ≡
            2 * ((p + 1) / 5 : ℕ) - 8 [ZMOD 16])) := by
  have hcast : ((5 * p : ℕ) : ℤ) = 5 * p := by push_cast; ring
  have h5p : (5 * p : ℤ) ≠ 0 := by have := hp.out.pos; positivity
  set A := ∑ x ∈ (range p).filter (fun x => x % 5 = 0 ∨ x % 5 = 4), legendreSym p (x : ℤ)
  set B := ∑ x ∈ (range p).filter (fun x => x % 5 = 2), legendreSym p (x : ℤ)
  have hre := fifth_theta_re hp40
  have him := fifth_theta_im hp40
  have hR : (thetaSum p).re / (5 * p : ℕ) = A := by
    rw [hre, hcast, Int.mul_ediv_cancel_left _ h5p]
  have hI : (thetaSum p).im / (5 * p : ℕ) = -B := by
    rw [him, hcast, ← mul_neg, Int.mul_ediv_cancel_left _ h5p]
  have hpart := fifth_partition (p := p)
  rw [fifth_leg_sum_zero (by omega), fifth_t3 hp40, fifth_t1 hp40, fifth_sum_J hp40] at hpart
  have hM := fifth_multCorr hp40
  rw [fifth_count_H hp40] at hM
  have hE := fifth_mem_iff_even hp40
  rw [fifth_count_H hp40, Nat.even_iff] at hE
  rw [hR, hI, hcast, hre, him, fifth_defect hp40, one_mul, hE]
  refine ⟨⟨A, rfl⟩, ⟨-B, by ring⟩, by omega, by omega, ?_, fun _ => ?_⟩
  · rw [Int.modEq_iff_dvd]; omega
  · rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd]; omega

end BandParityTower
