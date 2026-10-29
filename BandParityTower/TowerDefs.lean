module

public import BandParityTower.Defs
public import BandParityTower.Laws

@[expose] public section

/-!
# Definitions for the tower

Throughout `p` is a prime and `x.val` the least nonnegative residue of `x : ZMod p`.

* `twoVal p = a = v₂(p - 1)` and `oddPart p = m = (p - 1)/2^a`.
* `Ha p = H_a = {x : x^m = 1}`, the subgroup of order `m` of `(ℤ/p)ˣ`; the set
  `{x : x^{2m} = 1} = ± H_a` is the group of `2^{a-1}`-th power residues.
* `cosetOf c S = c S`, the image of `S` under `x ↦ c x`.
* `fTower p = f_a = ∑_{u ∈ H_a} s(u) s(u²)` and `eTower p = e_a = ∑_{u ∈ 2H_a} s(u) s(u²)`.
* `powResCount k p = #{0 < n < p/4 : n is a k-th power residue}` and
  `Na p = N_a = powResCount 2^{a-1} p`.
* `bandSignE e x = (-1)^{⌊⟨x⟩^e/p⌋}` and `pairBandSum X e`, the band-parity sum of the pair of
  cosets `X ∪ (-X)` over `(0, p/2)`, with sign `+1` on `X` and `-1` on `-X`.
* `oddCountZ S = α(S)`, the number of elements of `S` with odd least residue.
* `bandSumPow χ e = 𝒞_e = ∑_{0 < n < p/2} χ(n) (-1)^{⌊n^e/p⌋}`.
-/

namespace BandParityTower

open Finset

/-- `a = v₂(p - 1)`. -/
def twoVal (p : ℕ) : ℕ := padicValNat 2 (p - 1)

/-- `m = (p - 1)/2^a`, the odd part of `p - 1`. -/
def oddPart (p : ℕ) : ℕ := (p - 1) / 2 ^ twoVal p

variable {p : ℕ} [hp : Fact p.Prime]

/-- `H_a = {x : x^m = 1}`, the subgroup of `(ℤ/p)ˣ` of order `m`. -/
def Ha (p : ℕ) [Fact p.Prime] : Finset (ZMod p) := univ.filter fun x => x ^ oddPart p = 1

/-- The coset `c S = {c x : x ∈ S}`. -/
def cosetOf (c : ZMod p) (S : Finset (ZMod p)) : Finset (ZMod p) := S.image (c * ·)

/-- `f_a = ∑_{u ∈ H_a} s(u) s(u²)`. -/
def fTower (p : ℕ) [Fact p.Prime] : ℤ := ∑ x ∈ Ha p, parSign x * parSign (x ^ 2)

/-- `e_a = ∑_{u ∈ 2 H_a} s(u) s(u²)`. -/
def eTower (p : ℕ) [Fact p.Prime] : ℤ := ∑ x ∈ cosetOf 2 (Ha p), parSign x * parSign (x ^ 2)

/-- The number of `k`-th power residues in `(0, p/4)`. -/
def powResCount (k p : ℕ) [Fact p.Prime] : ℕ :=
  ((range p).filter fun n => 0 < n ∧ 4 * n < p ∧ ∃ y : ZMod p, y ^ k = (n : ZMod p)).card

/-- `N_a`, the number of `2^{a-1}`-th power residues in `(0, p/4)`. -/
def Na (p : ℕ) [Fact p.Prime] : ℕ := powResCount (2 ^ (twoVal p - 1)) p

/-- The band sign `(-1)^{⌊⟨x⟩^e/p⌋}`. -/
def bandSignE (e : ℕ) (x : ZMod p) : ℤ := (-1) ^ (x.val ^ e / p)

/-- The band-parity sum of the pair of cosets `X ∪ (-X)` over `(0, p/2)`, with sign `+1` on `X`
and `-1` on `-X`. -/
def pairBandSum (X : Finset (ZMod p)) (e : ℕ) : ℤ :=
  ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p ∧ (n ∈ X ∨ -n ∈ X)),
    (if n ∈ X then 1 else -1) * bandSignE e n

/-- `α(S)`: the number of elements of `S` with odd least residue. -/
def oddCountZ (S : Finset (ZMod p)) : ℕ := (S.filter fun x => Odd x.val).card

/-- `𝒞_e = ∑_{0 < n < p/2} χ(n) (-1)^{⌊n^e/p⌋}`. -/
def bandSumPow {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) (e : ℕ) : R :=
  ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p), χ n * (bandSignE e n : R)

end BandParityTower
