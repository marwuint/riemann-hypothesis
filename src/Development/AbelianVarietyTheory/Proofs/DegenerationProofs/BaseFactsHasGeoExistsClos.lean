import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseFactsOfIsEE
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasGradedChartsNearGenericPointClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyAbelianSchemeProjectiveClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyClosureExtensionAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureTestsExistAndReductionIndependent
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasGeometricTestOfHasUniformisedTest
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreEqSpecialFibreOfReductionIndep
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem baseFacts_hasGeo_exists_clos : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Big → ρ.HasU → S.Over₀ M U₀ → S.IsEE M U₀ EE → BaseFacts S M U₀ EE ∧ ρ.HasGeo ∧ ∃ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), ex.core.HasTests ∧ ex.core.Indep ∧ ex.core.Fib ∧ ex.core.HasCharts := by
  intro hL hT o Ω _ _ _ _ S ρ M U₀ EE hB hU hO hE
  have hTests : S.HasTests := by
    intro p _ y hy
    obtain ⟨_, _, τ, _⟩ := hU p y hy ∅
    exact ⟨τ⟩
  have hF : BaseFacts S M U₀ EE := baseFacts_of_isEE o Ω S M U₀ EE hTests hO hE
  have hG : ρ.HasGeo := _root_.GlobalTheory.ZH.GeoExist.hasGeo_of_hasU hL hT o Ω S ρ hB hU
  obtain ⟨Q⟩ := _root_.GlobalTheory.ZH.nonempty_clos hL o Ω S ρ M U₀ EE hF
  obtain ⟨ex⟩ := _root_.GlobalTheory.ZH.ClosureLifting.nonempty_ext hL o Ω S ρ M U₀ EE hF Q
  obtain ⟨h₁, h₂⟩ := _root_.GlobalTheory.ZH.Clos.Ext.hasTests_and_indep hL o Ω S ρ M U₀ EE hF Q ex hB hG
  have h₃ : ex.core.Fib := _root_.GlobalTheory.ZJ.Core.fib_of_indep ex.core h₂
  exact ⟨hF, hG, Q, ex, h₁, h₂, h₃, _root_.GlobalTheory.ZH.GradedCharts.hasCharts hL o Ω S ρ M U₀ EE hF Q ex hB hG h₃⟩

end GlobalTheory.ZH
