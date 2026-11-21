import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentFlagVec
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.PsJetEqToJetOfNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam.Pad GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps

namespace GlobalTheory.BdFib

attribute [local instance] Over.cartesianMonoidalCategory

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

def FibAt {k : Type} [Field k] (x : Sp k ⟶ X) (φ : Fib k) (m : CubeMap φ.G t.G) : Prop :=
  IsGrpPullback φ.G t.G x m.F ∧ m.e = x ∧ m.IsPullCubical φ.cub t.cub

variable {t}

end Fibre

section Large

variable {Y : Scheme.{0}}

def Large (y : Sp Qb ⟶ Y) (Q : ∀ (K : Type) [Field K] [NumberField K], (Sp K ⟶ Y) → Prop) : Prop :=
  ∃ (K₀ : Type) (_ : Field K₀) (_ : NumberField K₀) (io₀ : K₀ →+* Qb),
    ∀ (K : Type) [Field K] [NumberField K] (io : K →+* Qb) (j : K₀ →+* K), io.comp j = io₀ →
      ∀ yK : Sp K ⟶ Y, spMap io ≫ yK = y → Q K yK

theorem exists_common {K₁ K₂ : Type} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂] (i₁ : K₁ →+* Qb)
    (i₂ : K₂ →+* Qb) : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (i : K →+* Qb) (j₁ : K₁ →+* K) (j₂ : K₂ →+* K),
      i.comp j₁ = i₁ ∧ i.comp j₂ = i₂ := by
  let a₁ : K₁ →ₐ[ℚ] Qb := i₁.toRatAlgHom
  let a₂ : K₂ →ₐ[ℚ] Qb := i₂.toRatAlgHom
  haveI : FiniteDimensional ℚ a₁.fieldRange := a₁.toLinearMap.finiteDimensional_range
  haveI : FiniteDimensional ℚ a₂.fieldRange := a₂.toLinearMap.finiteDimensional_range
  let K : IntermediateField ℚ Qb := a₁.fieldRange ⊔ a₂.fieldRange
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_sup _ _
  haveI : NumberField K := ⟨⟩
  refine ⟨K, inferInstance, inferInstance, algebraMap K Qb,
    i₁.codRestrict K.toSubfield fun a => (le_sup_left : a₁.fieldRange ≤ K) ⟨a, rfl⟩,
    i₂.codRestrict K.toSubfield fun a => (le_sup_right : a₂.fieldRange ≤ K) ⟨a, rfl⟩, rfl, rfl⟩

variable {y : Sp Qb ⟶ Y} {Q Q' : ∀ (K : Type) [Field K] [NumberField K], (Sp K ⟶ Y) → Prop}

theorem Large.and (h : Large y Q) (h' : Large y Q') : Large y fun K _ _ yK => Q K yK ∧ Q' K yK := by
  obtain ⟨K₁, _, _, i₁, h₁⟩ := h
  obtain ⟨K₂, _, _, i₂, h₂⟩ := h'
  obtain ⟨K₀, _, _, i, j₁, j₂, e₁, e₂⟩ := exists_common i₁ i₂
  refine ⟨K₀, _, inferInstance, i, fun K _ _ io j hj yK hy => ⟨h₁ K io (j.comp j₁) ?_ yK hy, h₂ K io (j.comp j₂) ?_ yK hy⟩⟩
  · rw [← RingHom.comp_assoc, hj, e₁]
  · rw [← RingHom.comp_assoc, hj, e₂]

end Large

end GlobalTheory.BdFib

end
