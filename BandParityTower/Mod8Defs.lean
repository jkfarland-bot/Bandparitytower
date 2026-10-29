module

public import BandParityTower.TowerDefs

@[expose] public section

/-!
# Definitions for the analysis modulo eight

* `jointOdd X = Δ(X) = #{u ∈ X : ⟨u⟩ and ⟨u²⟩ both odd}`.
* `multCorr a = M_H(a) = ∑_{u ∈ H} s(u) s(a u)` and `multCount a = C(a)`, the number of `u ∈ H`
  with `⟨u⟩` and `⟨a u⟩` both odd, for `H = H_a` (the fourth powers when `p ≡ 5 (mod 8)`).
* `oddInd x = ι(x) = [⟨x⟩ odd]` and `defect a = d(a) = ι(a) + ι(a⁻¹) mod 2`.
* `xi5 n = ξ(n)`, the quartic character modulo `5` with `ξ(2) = i`, and
  `thetaSum p = ∑_{n < 5p} θ_p(n) n = 5p B_{1,θ_p}` for `θ_p = (·/p) ξ`.
* `fifthCount p = R_5(p)`, the number of quadratic residues in `(p/5, 2p/5)`.
-/

namespace BandParityTower

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- `Δ(X)`: the number of `u ∈ X` with `⟨u⟩` and `⟨u²⟩` both odd. -/
def jointOdd (X : Finset (ZMod p)) : ℕ := (X.filter fun u => Odd u.val ∧ Odd (u ^ 2).val).card

/-- `M_H(a) = ∑_{u ∈ H} s(u) s(a u)`. -/
def multCorr (a : ZMod p) : ℤ := ∑ u ∈ Ha p, parSign u * parSign (a * u)

/-- `C(a) = #{u ∈ H : ⟨u⟩, ⟨a u⟩ both odd}`. -/
def multCount (a : ZMod p) : ℕ := ((Ha p).filter fun u => Odd u.val ∧ Odd (a * u).val).card

/-- `ι(x) = [⟨x⟩ odd]`. -/
def oddInd (x : ZMod p) : ℤ := if Odd x.val then 1 else 0

/-- `d(a) = ι(a) + ι(a⁻¹) mod 2`. -/
def defect (a : ZMod p) : ℤ := (oddInd a + oddInd a⁻¹) % 2

/-- The quartic character `ξ` modulo `5` with `ξ(2) = i`, as a function on `ℕ`. -/
def xi5 (n : ℕ) : GaussianInt :=
  if n % 5 = 1 then 1 else if n % 5 = 2 then gi else if n % 5 = 3 then -gi
  else if n % 5 = 4 then -1 else 0

/-- `5p B_{1,θ_p} = ∑_{0 ≤ n < 5p} θ_p(n) n` with `θ_p(n) = (n/p) ξ(n)`. -/
def thetaSum (p : ℕ) : GaussianInt :=
  ∑ n ∈ range (5 * p), ((legendreSym p n : ℤ) : GaussianInt) * xi5 n * (n : GaussianInt)

/-- `R_5(p)`: the number of quadratic residues in `(p/5, 2p/5)`. -/
def fifthCount (p : ℕ) [Fact p.Prime] : ℕ :=
  ((range p).filter fun n => p < 5 * n ∧ 5 * n < 2 * p ∧ legendreSym p n = 1).card

end BandParityTower
