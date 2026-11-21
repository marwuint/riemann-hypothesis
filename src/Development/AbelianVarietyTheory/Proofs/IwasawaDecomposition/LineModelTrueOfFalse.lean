import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsSMulRegularNatCast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DividesOfNormBoundedPoints

local macro "opens_le_auto" : tactic => `(tactic| (refine SetLike.le_def.2 fun z hz => ?_; simp only [TopologicalSpace.Opens.mem_inf] at hz ⊢; tauto))

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine.Twist

attribute [local instance] Over.cartesianMonoidalCategory

section Gen

variable {X : Scheme.{0}}

abbrev rs {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom

theorem res_val {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) : (res h a).val = rs h a.val := rfl

def PD (p : ℕ) {U : X.Opens} (x : Γ(X, U)) : Prop := ∃ N : ℕ, x ∣ (p : Γ(X, U)) ^ N

theorem PD.mul {p : ℕ} {U : X.Opens} {x y : Γ(X, U)} (hx : PD p x) (hy : PD p y) : PD p (x * y) := by
  obtain ⟨N, hN⟩ := hx
  obtain ⟨M, hM⟩ := hy
  exact ⟨N + M, pow_add (p : Γ(X, U)) N M ▸ mul_dvd_mul hN hM⟩

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

section Model

variable (Z : Mdl Y i₀)

theorem cancel (hp : p ≠ 0) {U : Z.X.Opens} (hU : IsAffineOpen U) {x y : Γ(Z.X, U)} (hx : PD p x) (h : x * y = 0) :
    y = 0 := by
  obtain ⟨N, c, hc⟩ := hx
  refine Z.isSMulRegular_natCast hU (pow_ne_zero N hp) ?_
  rw [Nat.cast_pow, hc, mul_comm x c, _root_.mul_assoc, h, mul_zero]

end Model

end GlobalTheory.HTLine.Twist
