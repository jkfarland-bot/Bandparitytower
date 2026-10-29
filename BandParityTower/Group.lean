module

public import BandParityTower.TowerDefs

@[expose] public section

/-!
# The cyclic group `(ℤ/p)ˣ`

Counting solutions of `x^d = 1`, the power residue criterion, and the arithmetic of
`a = v₂(p - 1)` and `m = (p - 1)/2^a`.
-/

namespace BandParityTower

open Finset

/-! ### `a` and `m` -/

lemma twoVal_eq_factorization (n : ℕ) : twoVal n = (n - 1).factorization 2 :=
  (Nat.factorization_def _ Nat.prime_two).symm

lemma two_pow_mul_oddPart {n : ℕ} (_hn : 2 ≤ n) : 2 ^ twoVal n * oddPart n = n - 1 := by
  unfold oddPart
  rw [twoVal_eq_factorization]
  exact Nat.ordProj_mul_ordCompl_eq_self (n - 1) 2

lemma oddPart_odd {n : ℕ} (hn : 2 ≤ n) : Odd (oddPart n) := by
  unfold oddPart
  rw [twoVal_eq_factorization]
  have h := Nat.coprime_ordCompl Nat.prime_two (show n - 1 ≠ 0 by omega)
  rw [Nat.coprime_two_left] at h
  exact h

lemma oddPart_pos {n : ℕ} (hn : 2 ≤ n) : 0 < oddPart n := (oddPart_odd hn).pos

lemma twoVal_ge_two {n : ℕ} (hn : n % 4 = 1) (h2 : 2 ≤ n) : 2 ≤ twoVal n := by
  rw [twoVal_eq_factorization]
  have h4 : 2 ^ 2 ∣ n - 1 := by omega
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)).1 h4

lemma twoVal_pos {n : ℕ} (hn : n % 2 = 1) (h2 : 3 ≤ n) : 1 ≤ twoVal n := by
  rw [twoVal_eq_factorization]
  have h4 : 2 ^ 1 ∣ n - 1 := by omega
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)).1 h4

/-- `p - 1 = 2^{a-1} (2m)` when `a ≥ 1`. -/
lemma two_pow_pred_mul {n : ℕ} (h2 : 2 ≤ n) (ha : 1 ≤ twoVal n) :
    2 ^ (twoVal n - 1) * (2 * oddPart n) = n - 1 := by
  rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel ha, two_pow_mul_oddPart h2]

variable {p : ℕ} [hp : Fact p.Prime]

lemma prime_two_le : 2 ≤ p := hp.out.two_le

/-! ### A generator -/

/-- A generator of `(ℤ/p)ˣ`, seen in `ZMod p`. -/
lemma exists_gen : ∃ g : ZMod p, g ≠ 0 ∧ (∀ j : ℕ, g ^ j = 1 ↔ p - 1 ∣ j) ∧
    ∀ x : ZMod p, x ≠ 0 → ∃ j : ℕ, g ^ j = x := by
  obtain ⟨g, hgo, hg⟩ := exists_generator (p := p)
  refine ⟨g, g.ne_zero, fun j => ?_, fun x hx => ?_⟩
  · rw [← hgo, orderOf_dvd_iff_pow_eq_one, ← Units.val_pow_eq_pow_val]
    exact ⟨fun h => Units.ext h, fun h => by rw [h]; rfl⟩
  · obtain ⟨j, hj⟩ := hg (Units.mk0 x hx)
    exact ⟨j, by rw [← Units.val_pow_eq_pow_val, hj]; rfl⟩

lemma pow_sub_one_eq_one {x : ZMod p} (hx : x ≠ 0) : x ^ (p - 1) = 1 :=
  ZMod.pow_card_sub_one_eq_one hx

lemma ne_zero_of_pow_eq_one {x : ZMod p} {d : ℕ} (hd : d ≠ 0) (h : x ^ d = 1) : x ≠ 0 := by
  rintro rfl; rw [zero_pow hd] at h; exact zero_ne_one h

/-- **Counting roots of unity.** For `d ∣ p - 1` there are exactly `d` solutions of `x^d = 1`. -/
theorem card_pow_eq_one {d : ℕ} (hd : d ∣ p - 1) :
    (univ.filter fun x : ZMod p => x ^ d = 1).card = d := by
  have hp2 := prime_two_le (p := p)
  obtain ⟨g, -, hg1, hgx⟩ := exists_gen (p := p)
  obtain ⟨c, hc⟩ := hd
  have hd0 : d ≠ 0 := by rintro rfl; omega
  have hc0 : c ≠ 0 := by rintro rfl; omega
  have himg : (univ.filter fun x : ZMod p => x ^ d = 1) = (range d).image (fun i => g ^ (c * i)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_range]
    constructor
    · intro hx
      obtain ⟨j, rfl⟩ := hgx x (ne_zero_of_pow_eq_one hd0 hx)
      rw [← pow_mul, hg1, hc] at hx
      have : c ∣ j := by
        obtain ⟨q, hq⟩ := hx
        exact ⟨q, by
          have : j * d = c * q * d := by rw [hq]; ring
          rw [mul_comm d c] at hq
          exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hd0) (by linarith)⟩
      obtain ⟨i, rfl⟩ := this
      refine ⟨i % d, Nat.mod_lt _ (Nat.pos_of_ne_zero hd0), ?_⟩
      have : g ^ (c * i) = g ^ (c * (i % d)) * (g ^ (d * c)) ^ (i / d) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        conv_lhs => rw [← Nat.mod_add_div i d]
        ring
      have h1 : g ^ (d * c) = 1 := (hg1 _).2 (by rw [hc])
      rw [this, h1, one_pow, mul_one]
    · rintro ⟨i, -, rfl⟩
      rw [← pow_mul, hg1, hc]
      exact ⟨i, by ring⟩
  rw [himg, card_image_of_injOn, card_range]
  intro i hi j hj hij
  simp only [coe_range, Set.mem_Iio] at hi hj
  have key : ∀ i j, i < d → j < d → i ≤ j → g ^ (c * i) = g ^ (c * j) → i = j := by
    intro i j hi hj hle h
    have h1 : g ^ (c * (j - i)) = 1 := by
      have hg0 : g ^ (c * i) ≠ 0 := pow_ne_zero _ (by
        intro h0; have := (hg1 (p - 1)).2 dvd_rfl; rw [h0, zero_pow (by omega)] at this
        exact zero_ne_one this)
      have : g ^ (c * j) = g ^ (c * i) * g ^ (c * (j - i)) := by
        rw [← pow_add]; congr 1; rw [← mul_add, Nat.add_sub_cancel' hle]
      rw [← h, eq_comm] at this
      exact (mul_eq_left₀ hg0).1 this
    rw [hg1, hc] at h1
    by_contra hne
    have hlt : 0 < j - i := by omega
    have := Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hc0) hlt) h1
    have : c * (j - i) < c * d := Nat.mul_lt_mul_of_pos_left (by omega) (Nat.pos_of_ne_zero hc0)
    rw [mul_comm d c] at *
    omega
  rcases le_total i j with h | h
  · exact key i j hi hj h hij
  · exact (key j i hj hi h hij.symm).symm

/-- **Power residue criterion.** For `k ∣ p - 1` and `x ≠ 0`, `x` is a `k`-th power exactly when
`x^{(p-1)/k} = 1`. -/
theorem exists_pow_iff {k : ℕ} (hk : k ∣ p - 1) {x : ZMod p} (hx : x ≠ 0) :
    (∃ y : ZMod p, y ^ k = x) ↔ x ^ ((p - 1) / k) = 1 := by
  have hp2 := prime_two_le (p := p)
  obtain ⟨c, hc⟩ := hk
  have hk0 : k ≠ 0 := by rintro rfl; omega
  have hck : (p - 1) / k = c := by rw [hc]; exact Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hk0)
  rw [hck]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by rintro rfl; exact hx (zero_pow hk0)
    rw [← pow_mul, ← hc]; exact pow_sub_one_eq_one hy
  · intro h
    obtain ⟨g, -, hg1, hgx⟩ := exists_gen (p := p)
    obtain ⟨j, rfl⟩ := hgx x hx
    rw [← pow_mul, hg1, hc] at h
    have hc0 : c ≠ 0 := by rintro rfl; omega
    obtain ⟨q, hq⟩ := h
    have : j = k * q := by
      have : j * c = k * q * c := by rw [hq]; ring
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hc0) this
    exact ⟨g ^ q, by rw [← pow_mul, mul_comm, this]⟩

/-- `x^m = 1` and `x^{2m} = 1` as power residue conditions. -/
lemma mem_Ha_iff (x : ZMod p) : x ∈ Ha p ↔ x ^ oddPart p = 1 := by simp [Ha]

lemma card_Ha : (Ha p).card = oddPart p :=
  card_pow_eq_one ⟨2 ^ twoVal p, by rw [mul_comm, two_pow_mul_oddPart prime_two_le]⟩

lemma card_pmHa (ha : 1 ≤ twoVal p) :
    (univ.filter fun x : ZMod p => x ^ (2 * oddPart p) = 1).card = 2 * oddPart p :=
  card_pow_eq_one ⟨2 ^ (twoVal p - 1), by rw [mul_comm, two_pow_pred_mul prime_two_le ha]⟩

/-- `x` is a `2^{a-1}`-th power residue iff `x^{2m} = 1`. -/
lemma exists_pow_pred_iff (ha : 1 ≤ twoVal p) {x : ZMod p} (hx : x ≠ 0) :
    (∃ y : ZMod p, y ^ 2 ^ (twoVal p - 1) = x) ↔ x ^ (2 * oddPart p) = 1 := by
  have h := two_pow_pred_mul (prime_two_le (p := p)) ha
  rw [exists_pow_iff ⟨_, h.symm⟩ hx, ← h,
    Nat.mul_div_cancel_left _ (by positivity)]

/-- `x` is a `2^a`-th power residue iff `x ∈ H_a`. -/
lemma exists_pow_top_iff {x : ZMod p} (hx : x ≠ 0) :
    (∃ y : ZMod p, y ^ 2 ^ twoVal p = x) ↔ x ^ oddPart p = 1 := by
  have h := two_pow_mul_oddPart (prime_two_le (p := p))
  rw [exists_pow_iff ⟨_, h.symm⟩ hx, ← h, Nat.mul_div_cancel_left _ (by positivity)]

end BandParityTower
