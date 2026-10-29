module

public import BandParityTower.Cycles

@[expose] public section

/-!
# The real bit reduced to multipliers (Lemma 5.7, Proposition 5.8)

For an odd prime `p` and `H = H_a`, with `α = α(H)`, `M_H(a) = ∑_{u ∈ H} s(u) s(au)` and
`C(a) = #{u ∈ H : ⟨u⟩, ⟨au⟩ odd}`:

* `multCorr_eq`: `M_H(a) = m - 4α + 4C(a)` for `a ∈ H`;
* `sum_multCount`: `∑_{a ∈ H} C(a) = α²`;
* `defect_lemma`: `2(f_a - m) ≡ ∑_{a ∈ H, a ≠ a⁻¹} d(a) (M_H(a) - m) (mod 16)`, which is the
  paper's `f ≡ Q + ∑_{{a, a⁻¹}} d(a)(M_H(a) - Q) (mod 8)` with each pair counted from both ends
  (the summand is the same at `a` and `a⁻¹`). The paper states it at `p ≡ 5 (mod 8)`, where
  `m = Q` and `f_a = f`; the argument works for every odd prime.
* `odd_multiplier` (Proposition 5.8): for `p ≡ 5 (mod 8)` and odd `a > 0` prime to `p`,
  `M_H(a) = ∑_{u ∈ H} (-1)^{⌊a⟨u⟩/p⌋} = ¼ ∑_{0 < n < p} (1 + (n/p)) (-1)^{⌊an/p⌋}`.
-/

namespace BandParityTower

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
lemma oddInd_eq (x : ZMod p) : oddInd x = 0 ∨ oddInd x = 1 := by
  unfold oddInd; split_ifs <;> simp

omit hp in
lemma parSign_eq_oddInd (x : ZMod p) : parSign x = 1 - 2 * oddInd x := by
  unfold parSign oddInd
  rcases Nat.even_or_odd x.val with h | h
  · rw [h.neg_one_pow, ite_eq_right (Nat.not_odd_iff_even.2 h)]; ring
  · rw [h.neg_one_pow, ite_eq_left h]; ring

omit hp in
lemma oddCountZ_eq_sum (S : Finset (ZMod p)) : (oddCountZ S : ℤ) = ∑ u ∈ S, oddInd u := by
  unfold oddCountZ oddInd; rw [sum_boole]

lemma multCount_eq_sum (a : ZMod p) :
    (multCount a : ℤ) = ∑ u ∈ Ha p, oddInd u * oddInd (a * u) := by
  unfold multCount oddInd
  rw [← sum_boole]
  refine sum_congr rfl fun u _ => ?_
  split_ifs <;> simp_all

lemma jointOdd_eq_sum (X : Finset (ZMod p)) :
    (jointOdd X : ℤ) = ∑ u ∈ X, oddInd u * oddInd (u ^ 2) := by
  unfold jointOdd oddInd
  rw [← sum_boole]
  refine sum_congr rfl fun u _ => ?_
  split_ifs <;> simp_all

/-- `#{u ∈ H : ⟨au⟩ odd} = α(H)` for `a ∈ H`. -/
lemma sum_oddInd_mul {a : ZMod p} (ha : a ∈ Ha p) :
    ∑ u ∈ Ha p, oddInd (a * u) = ∑ u ∈ Ha p, oddInd u := by
  have ha0 := ne_zero_of_mem_Ha ha
  exact sum_nbij' (fun u => a * u) (fun w => a⁻¹ * w) (fun u hu => mul_mem_Ha ha hu)
    (fun w hw => mul_mem_Ha (inv_mem_Ha ha) hw)
    (fun u _ => by rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul])
    (fun w _ => by rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]) (fun _ _ => rfl)

/-- **Lemma 5.7 (first identity).** `M_H(a) = m - 4α + 4C(a)` for `a ∈ H`. -/
theorem multCorr_eq' {a : ZMod p} (ha : a ∈ Ha p) :
    multCorr a = oddPart p - 4 * oddCountZ (Ha p) + 4 * multCount a := by
  unfold multCorr
  simp only [parSign_eq_oddInd]
  rw [multCount_eq_sum, oddCountZ_eq_sum]
  have h := sum_oddInd_mul ha
  have hc : ((Ha p).card : ℤ) = oddPart p := by rw [card_Ha]
  rw [← hc]
  have : ∀ u ∈ Ha p, (1 - 2 * oddInd u) * (1 - 2 * oddInd (a * u)) =
      1 - 2 * oddInd u - 2 * oddInd (a * u) + 4 * (oddInd u * oddInd (a * u)) :=
    fun u _ => by ring
  rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum,
    ← mul_sum, ← mul_sum, h, sum_const, nsmul_eq_mul, mul_one]
  ring

/-- **Lemma 5.7 (second identity).** `∑_{a ∈ H} C(a) = α²`. -/
theorem sum_multCount' : ∑ a ∈ Ha p, (multCount a : ℤ) = (oddCountZ (Ha p) : ℤ) ^ 2 := by
  simp only [multCount_eq_sum, oddCountZ_eq_sum, sq, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun u hu => ?_
  rw [← mul_sum, ← mul_sum]
  congr 1
  simp_rw [mul_comm _ u]
  exact sum_oddInd_mul hu

/-! ### Parity of sums over symmetric pairs -/

omit hp in
/-- A sum of an integer function over a set carrying a fixed-point-free involution that preserves
the function is even. -/
lemma even_sum_of_involution {ι : Type*} (S : Finset ι) (g : ι → ℤ) (σ : ι → ι)
    (hσS : ∀ x ∈ S, σ x ∈ S) (hσσ : ∀ x ∈ S, σ (σ x) = x) (hfix : ∀ x ∈ S, σ x ≠ x)
    (hg : ∀ x ∈ S, g (σ x) = g x) : Even (∑ x ∈ S, g x) := by
  have h : ((∑ x ∈ S, g x : ℤ) : ZMod 2) = 0 := by
    push_cast
    refine sum_involution (fun x _ => σ x) (fun x hx => ?_) (fun x hx _ => hfix x hx)
      (fun x hx => hσS x hx) (fun x hx => hσσ x hx)
    rw [hg x hx, ← two_mul]
    exact mul_eq_zero_of_left (by decide) _
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact even_iff_two_dvd.2 (by exact_mod_cast h)

lemma eq_inv_iff_eq_one (hp2 : p ≠ 2) {a : ZMod p} (ha : a ∈ Ha p) : a = a⁻¹ ↔ a = 1 := by
  have ha0 := ne_zero_of_mem_Ha ha
  constructor
  · intro h
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ ha0
    rcases mul_self_eq_one_iff.1 h2 with h' | h'
    · exact h'
    · exact absurd (h' ▸ ha) (neg_one_not_mem_Ha hp2)
  · rintro rfl; rw [inv_one]

lemma multCount_inv {a : ZMod p} (ha : a ∈ Ha p) : multCount a⁻¹ = multCount a := by
  have ha0 := ne_zero_of_mem_Ha ha
  unfold multCount
  refine card_nbij' (fun u => a⁻¹ * u) (fun w => a * w) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [mem_coe, mem_filter] at hu ⊢
    refine ⟨mul_mem_Ha (inv_mem_Ha ha) hu.1, hu.2.2, ?_⟩
    rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]; exact hu.2.1
  · intro w hw
    simp only [mem_coe, mem_filter] at hw ⊢
    refine ⟨mul_mem_Ha ha hw.1, hw.2.2, ?_⟩
    rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]; exact hw.2.1
  · intro u _; simp only; rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
  · intro w _; simp only; rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]

lemma oddInd_one (_hp2 : p ≠ 2) : oddInd (1 : ZMod p) = 1 := by
  unfold oddInd
  have : (1 : ZMod p).val = 1 := by
    have : Fact (1 < p) := ⟨hp.out.one_lt⟩
    exact ZMod.val_one p
  rw [this]; simp

omit hp in
lemma defect_eq (x : ZMod p) :
    defect x = oddInd x + oddInd x⁻¹ - 2 * (oddInd x * oddInd x⁻¹) := by
  unfold defect
  rcases oddInd_eq x with h | h <;> rcases oddInd_eq x⁻¹ with h' | h' <;> rw [h, h'] <;> norm_num

/-- **Lemma 5.7 (the defect congruence).** -/
theorem defect_lemma' (hp2 : p ≠ 2) :
    2 * (fTower p - oddPart p) ≡ ∑ a ∈ (Ha p).filter (fun a => a ≠ a⁻¹),
      defect a * (multCorr a - oddPart p) [ZMOD 16] := by
  set H := Ha p
  set α : ℤ := (oddCountZ H : ℤ)
  set H' := H.filter (fun a => a ≠ a⁻¹)
  have hH' : H' = H.erase 1 := by
    ext a
    simp only [H', mem_filter, mem_erase]
    constructor
    · rintro ⟨ha, hne⟩; exact ⟨fun h => hne ((eq_inv_iff_eq_one hp2 ha).2 h), ha⟩
    · rintro ⟨hne, ha⟩; exact ⟨ha, fun h => hne ((eq_inv_iff_eq_one hp2 ha).1 h)⟩
  have h1H : (1 : ZMod p) ∈ H := by rw [mem_Ha_iff, one_pow]
  have hinvS : ∀ a ∈ H', a⁻¹ ∈ H' := by
    intro a ha
    simp only [H', mem_filter] at ha ⊢
    exact ⟨inv_mem_Ha ha.1, by rw [inv_inv]; exact fun h => ha.2 h.symm⟩
  have hfix : ∀ a ∈ H', a⁻¹ ≠ a := fun a ha h => (mem_filter.1 ha).2 h.symm
  have hmem : ∀ a ∈ H', a ∈ H := fun a ha => (mem_filter.1 ha).1
  -- `f = m - 4α + 4Δ`
  have hf : fTower p = oddPart p - 4 * α + 4 * jointOdd H := by
    have h := sum_sq_exact H
    have hsq : (H.filter fun x => Odd (x ^ 2).val).card = oddCountZ H := by
      have hb := sq_bijOn_coset hp2 (one_ne_zero (α := ZMod p))
      simp only [cosetOf_one, one_pow] at hb
      unfold oddCountZ
      exact card_nbij (fun x => x ^ 2) (fun x hx => mem_filter.2 ⟨hb.mapsTo (mem_filter.1 hx).1,
        (mem_filter.1 hx).2⟩)
        (fun x hx y hy h => hb.injOn (mem_filter.1 hx).1 (mem_filter.1 hy).1 h)
        (fun y hy => by
          obtain ⟨x, hx, rfl⟩ := hb.surjOn (mem_filter.1 hy).1
          exact ⟨x, mem_filter.2 ⟨hx, (mem_filter.1 hy).2⟩, rfl⟩)
    rw [hsq, card_Ha] at h
    unfold fTower; rw [h]; ring
  -- `Δ ≡ ∑_a ι(a) C(a) (mod 2)`
  set S : ℤ := ∑ a ∈ H', oddInd a * multCount a
  have hT : Even (∑ a ∈ H, oddInd a * multCount a - jointOdd H) := by
    have hT : ∑ a ∈ H, oddInd a * (multCount a : ℤ) =
        ∑ x ∈ H ×ˢ H, oddInd x.1 * (oddInd x.2 * oddInd (x.1 * x.2)) := by
      rw [sum_product]
      refine sum_congr rfl fun a _ => ?_
      rw [multCount_eq_sum, mul_sum]
    have hD : (jointOdd H : ℤ) =
        ∑ x ∈ (H ×ˢ H).filter (fun x => x.1 = x.2),
          oddInd x.1 * (oddInd x.2 * oddInd (x.1 * x.2)) := by
      rw [jointOdd_eq_sum]
      refine (sum_nbij' (fun u => (u, u)) (fun x => x.1) ?_ ?_ ?_ ?_ ?_)
      · intro u hu; simp [hu]
      · intro x hx; exact (mem_product.1 (mem_filter.1 hx).1).1
      · intro u _; rfl
      · intro x hx; have := (mem_filter.1 hx).2; ext <;> simp [this]
      · intro u _
        simp only
        rcases oddInd_eq u with h | h <;> rw [h, sq] <;> ring
    rw [hT, hD, ← sum_filter_add_sum_filter_not (H ×ˢ H) (fun x => x.1 = x.2), add_sub_cancel_left]
    refine even_sum_of_involution _ _ (fun x => (x.2, x.1)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_filter, mem_product] at hx ⊢
      exact ⟨⟨hx.1.2, hx.1.1⟩, fun h => hx.2 h.symm⟩
    · intro x _; rfl
    · intro x hx h
      simp only [mem_filter] at hx
      exact hx.2 (Prod.ext_iff.1 h).2
    · intro x _; simp only; rw [mul_comm x.2 x.1]; ring
  have hsplit : ∑ a ∈ H, oddInd a * (multCount a : ℤ) = α + S := by
    rw [← add_sum_erase H _ h1H, oddInd_one hp2, one_mul, ← hH']
    congr 1
    simp only [multCount, one_mul, and_self]
    rfl
  -- reindexing by inversion
  have hrei : ∑ a ∈ H', oddInd a⁻¹ * (multCount a : ℤ) = S :=
    sum_nbij' (fun a => a⁻¹) (fun a => a⁻¹) hinvS hinvS (fun a _ => inv_inv a)
      (fun a _ => inv_inv a) (fun a ha => by rw [multCount_inv (hmem a ha)])
  have hE1 : Even (∑ a ∈ H', oddInd a * oddInd a⁻¹ * (multCount a : ℤ)) :=
    even_sum_of_involution _ _ (fun a => a⁻¹) hinvS (fun a _ => inv_inv a) hfix
      (fun a ha => by rw [inv_inv, multCount_inv (hmem a ha)]; ring)
  have hE2 : Even (∑ a ∈ H', oddInd a * oddInd a⁻¹) :=
    even_sum_of_involution _ _ (fun a => a⁻¹) hinvS (fun a _ => inv_inv a) hfix
      (fun a _ => by rw [inv_inv]; ring)
  have hsumι : ∑ a ∈ H', oddInd a = α - 1 := by
    rw [hH', show α = ∑ u ∈ H, oddInd u from oddCountZ_eq_sum H, ← add_sum_erase H _ h1H,
      oddInd_one hp2]; ring
  have hsumι' : ∑ a ∈ H', oddInd a⁻¹ = α - 1 := by
    rw [← hsumι]
    exact sum_nbij' (fun a => a⁻¹) (fun a => a⁻¹) hinvS hinvS (fun a _ => inv_inv a)
      (fun a _ => inv_inv a) (fun a _ => rfl)
  -- the right-hand side
  have hrhs : ∑ a ∈ H', defect a * (multCorr a - oddPart p) =
      4 * (2 * S - 2 * ∑ a ∈ H', oddInd a * oddInd a⁻¹ * (multCount a : ℤ)) -
        4 * α * (2 * (α - 1) - 2 * ∑ a ∈ H', oddInd a * oddInd a⁻¹) := by
    have : ∀ a ∈ H', defect a * (multCorr a - oddPart p) =
        4 * (oddInd a * multCount a + oddInd a⁻¹ * multCount a -
          2 * (oddInd a * oddInd a⁻¹ * multCount a)) -
        4 * α * (oddInd a + oddInd a⁻¹ - 2 * (oddInd a * oddInd a⁻¹)) := by
      intro a ha
      rw [defect_eq, multCorr_eq' (hmem a ha)]; ring
    rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_sub_distrib,
      sum_add_distrib, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, hrei, hsumι,
      hsumι']
    ring
  rw [hrhs, hf]
  obtain ⟨e1, he1⟩ := hE1
  obtain ⟨e2, he2⟩ := hE2
  obtain ⟨w, hw⟩ := hT
  obtain ⟨z, hz⟩ := Int.even_mul_pred_self α
  rw [hsplit] at hw
  rw [he1, he2]
  apply Int.modEq_iff_dvd.2
  exact ⟨w - e1 - z + α * e2, by linear_combination 8 * hw - 8 * hz⟩

/-! ### Odd multipliers (Proposition 5.8) -/

lemma val_natCast_mul (a : ℕ) (u : ZMod p) : ((a : ZMod p) * u).val = a * u.val % p := by
  rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]

/-- `s(u) s(au) = (-1)^{⌊a⟨u⟩/p⌋}` for odd `a`. -/
lemma parSign_mul_odd (hp2 : p ≠ 2) {a : ℕ} (ha : Odd a) (u : ZMod p) :
    parSign u * parSign ((a : ZMod p) * u) = (-1) ^ (a * u.val / p) := by
  unfold parSign
  rw [val_natCast_mul]
  set v := u.val
  have hpo := odd_prime hp2
  have h1 : (-1 : ℤ) ^ (a * v) = (-1) ^ v := by
    rcases Nat.even_or_odd v with h | h
    · rw [h.neg_one_pow, (h.mul_left a).neg_one_pow]
    · rw [h.neg_one_pow, (ha.mul h).neg_one_pow]
  have h2 : (-1 : ℤ) ^ (a * v) = (-1) ^ (a * v / p) * (-1) ^ (a * v % p) := by
    conv_lhs => rw [← Nat.div_add_mod (a * v) p]
    rw [pow_add, pow_mul, hpo.neg_one_pow]
  have hr : (-1 : ℤ) ^ (a * v % p) * (-1) ^ (a * v % p) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have E := h1.symm.trans h2
  linear_combination ((-1 : ℤ) ^ (a * v % p)) * E + ((-1 : ℤ) ^ (a * v / p)) * hr

/-- The floor sign is invariant under `n ↦ p - n` for odd `a` prime to `p`. -/
lemma floor_sign_reflect {a : ℕ} (ha : Odd a) (hpa : ¬ p ∣ a) {n : ℕ} (hn0 : 0 < n) (hnp : n < p) :
    (-1 : ℤ) ^ (a * (p - n) / p) = (-1) ^ (a * n / p) := by
  have hp1 := hp.out.one_lt
  have hnd : ¬ p ∣ a * n := by
    intro h
    rcases (Nat.Prime.dvd_mul hp.out).1 h with h' | h'
    · exact hpa h'
    · exact absurd (Nat.le_of_dvd hn0 h') (by omega)
  set q := a * n / p
  set r := a * n % p
  have hr0 : 0 < r := Nat.pos_of_ne_zero (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
  have hrp : r < p := Nat.mod_lt _ (by omega)
  have han : a * n = p * q + r := (Nat.div_add_mod _ _).symm
  have hqa : q + 1 ≤ a := by
    by_contra h
    push Not at h
    have : a * n < a * p := Nat.mul_lt_mul_of_pos_left hnp (ha.pos)
    have : p * a ≤ p * q := Nat.mul_le_mul_left p (by omega)
    nlinarith
  have hsub : a * (p - n) = p * (a - q - 1) + (p - r) := by
    rw [Nat.mul_sub, mul_comm a p, han]
    have : p * a = p * (a - q - 1) + p * q + p := by
      rw [← mul_add, ← Nat.mul_succ]; congr 1; omega
    omega
  have hdiv : a * (p - n) / p = a - q - 1 := by
    rw [hsub, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), add_zero]
  rw [hdiv]
  obtain ⟨b, hb⟩ := ha
  rcases Nat.even_or_odd q with ⟨c, hc⟩ | ⟨c, hc⟩
  · rw [hc, Even.neg_one_pow ⟨c, rfl⟩, Even.neg_one_pow ⟨b - c, by omega⟩]
  · rw [hc, Odd.neg_one_pow ⟨c, rfl⟩, Odd.neg_one_pow ⟨b - c - 1, by omega⟩]

/-- **Proposition 5.8, odd multipliers are floor sums.** For `p ≡ 5 (mod 8)` and odd `a > 0` prime
to `p`, `M_H(a) = ∑_{u ∈ H} (-1)^{⌊a⟨u⟩/p⌋} = ¼ ∑_{0 < n < p} (1 + (n/p)) (-1)^{⌊an/p⌋}`. -/
theorem odd_multiplier' (hp8 : p % 8 = 5) {a : ℕ} (ha : Odd a) (hpa : ¬ p ∣ a) :
    multCorr (a : ZMod p) = ∑ u ∈ Ha p, (-1 : ℤ) ^ (a * u.val / p) ∧
      4 * multCorr (a : ZMod p) = ∑ n ∈ (range p).filter (0 < ·),
        (1 + legendreSym p n) * (-1) ^ (a * n / p) := by
  have hp2 : p ≠ 2 := by omega
  have h1 : multCorr (a : ZMod p) = ∑ u ∈ Ha p, (-1 : ℤ) ^ (a * u.val / p) := by
    unfold multCorr
    exact sum_congr rfl fun u _ => parSign_mul_odd hp2 ha u
  refine ⟨h1, ?_⟩
  set g : ZMod p → ℤ := fun x => (-1) ^ (a * x.val / p)
  -- the right side as a sum over `ZMod p`
  have hR : ∑ n ∈ (range p).filter (0 < ·), (1 + legendreSym p n) * (-1 : ℤ) ^ (a * n / p) =
      ∑ x ∈ univ.filter (fun x : ZMod p => 0 < x.val), (1 + legendreSym p x.val) * g x :=
    (sum_filter_val (p := p) (fun v => 0 < v)
      (fun v => (1 + legendreSym p v) * (-1 : ℤ) ^ (a * v / p))).symm
  rw [hR, h1]
  -- `1 + (x/p) = 2 [x ∈ ± H]` for `x ≠ 0`
  have hleg : ∀ x : ZMod p, x ≠ 0 →
      1 + legendreSym p x.val = 2 * (if x ∈ Ha p ∨ -x ∈ Ha p then 1 else 0) := by
    intro x hx
    have hsq : (x ^ (2 * ((p - 1) / 4)) = 1) ↔ IsSquare x := by
      rw [show 2 * ((p - 1) / 4) = (p - 1) / 2 by omega, ← exists_pow_iff ⟨(p - 1) / 2, by omega⟩ hx]
      exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← hy]; ring⟩, fun ⟨y, hy⟩ => ⟨y, by rw [hy]; ring⟩⟩
    have hpm : (x ∈ Ha p ∨ -x ∈ Ha p) ↔ IsSquare x := by
      rw [pm_Ha_iff hp2, oddPart_five hp8]; exact hsq
    have hl : legendreSym p x.val = quadraticChar (ZMod p) x := by
      unfold legendreSym; simp
    rw [hl]
    by_cases h : IsSquare x
    · rw [(quadraticChar_one_iff_isSquare hx).2 h, ite_eq_left (hpm.2 h)]; norm_num
    · rw [quadraticChar_neg_one_iff_not_isSquare.2 h, ite_eq_right (fun h' => h (hpm.1 h'))]
      norm_num
  have hpos : univ.filter (fun x : ZMod p => 0 < x.val) = univ.filter (fun x : ZMod p => x ≠ 0) := by
    ext x; simp [Nat.pos_iff_ne_zero, ZMod.val_eq_zero]
  have hs2 : ∑ x ∈ univ.filter (fun x : ZMod p => x ≠ 0), (1 + legendreSym p x.val) * g x =
      ∑ x ∈ univ.filter (fun x : ZMod p => x ≠ 0),
        2 * (if x ∈ Ha p ∨ -x ∈ Ha p then (1 : ℤ) else 0) * g x :=
    sum_congr rfl fun x hx => by rw [hleg x (mem_filter.1 hx).2]
  rw [hpos, hs2]
  -- reduce to `H ∪ (-H)`
  have hHm : (Ha p).image (fun x => -x) = univ.filter (fun x : ZMod p => -x ∈ Ha p) := by
    ext x; simp only [mem_image, mem_filter, mem_univ, true_and]
    exact ⟨fun ⟨y, hy, hxy⟩ => by rw [← hxy, neg_neg]; exact hy, fun h => ⟨-x, h, neg_neg x⟩⟩
  have hsplit : ∑ x ∈ univ.filter (fun x : ZMod p => x ≠ 0),
      2 * (if x ∈ Ha p ∨ -x ∈ Ha p then (1 : ℤ) else 0) * g x =
      2 * (∑ x ∈ Ha p, g x + ∑ x ∈ Ha p, g (-x)) := by
    rw [mul_add, mul_sum, mul_sum, ← sum_image (s := Ha p) (g := fun x => -x)
      (f := fun x => 2 * g x) (fun x _ y _ h => neg_injective h), ← sum_union]
    · symm
      refine sum_subset_zero_on_sdiff ?_ ?_ ?_
      · intro x hx
        rw [mem_union] at hx
        simp only [mem_filter, mem_univ, true_and]
        rcases hx with h | h
        · exact ne_zero_of_mem_Ha h
        · obtain ⟨y, hy, rfl⟩ := mem_image.1 h; exact neg_ne_zero.2 (ne_zero_of_mem_Ha hy)
      · intro x hx
        rw [mem_sdiff, mem_union, hHm] at hx
        have : ¬ (x ∈ Ha p ∨ -x ∈ Ha p) := by
          rintro (h | h)
          · exact hx.2 (Or.inl h)
          · exact hx.2 (Or.inr (mem_filter.2 ⟨mem_univ _, h⟩))
        rw [ite_eq_right this]; ring
      · intro x hx
        rw [mem_union] at hx
        rcases hx with h | h
        · rw [ite_eq_left (Or.inl h)]; ring
        · rw [hHm, mem_filter] at h; rw [ite_eq_left (Or.inr h.2)]; ring
    · rw [disjoint_left]
      intro x hx hx'
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hx'
      exact neg_one_not_mem_Ha hp2 (by
        have := mul_mem_Ha hx (inv_mem_Ha hy)
        rwa [neg_mul, mul_inv_cancel₀ (ne_zero_of_mem_Ha hy)] at this)
  rw [hsplit]
  have hrefl : ∑ x ∈ Ha p, g (-x) = ∑ x ∈ Ha p, g x := by
    refine sum_congr rfl fun x hx => ?_
    have hx0 := ne_zero_of_mem_Ha hx
    simp only [g]
    rw [val_neg_eq hx0]
    exact floor_sign_reflect ha hpa (Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero]))
      (ZMod.val_lt x)
  rw [hrefl]; ring

end BandParityTower
