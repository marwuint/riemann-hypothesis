import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGfCOfSuppAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.BotExpand
theorem kernel_eq_sum_of_jets : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ → IsBottomTri W i j X →
    ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∃ (k : ℕ) (c : Fin k → ℂ) (w : Fin k → WO A' WW),
      (∀ l, IsAlgebraic ℚ (c l)) ∧ (∀ l, (w l).map (infPart D) = 0) ∧
      (∀ l, ∃ m : ℕ, 0 < m ∧ m • w l ∈ latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) ∧
      ∀ P : PolF D WW.rank A'.rank, X.ker' W.ψ W.θ t P h x =
        ∑ l, c l * pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (heisO W.ψ A' WW (w l) X.vac') P 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t x hx h hh
  have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
  have hv : IsVacO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ X.vac' := hX.is.isVac'
  have hθ : IsInfFam W.θ := hv.2.inf
  have hS : IsSelfDualC A' X.rA'.Λ := hX.is.rigA'.1
  have hT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hf := GlobalTheory.T.finiteDatum_isAlgebraicCombination_definiteBottom hX t
  obtain ⟨k, c, w, hc, hw, e⟩ := om_alg hv hS hT hW (om_vac_algComb hv hS hT (fun τ => (hX.is.rigA'.2.2 τ).1)
    (fun τ => (hX.is.rigW.2.2 τ).1) hW hx hh) hf
  refine ⟨k, c, w, hc, hw, fun l => GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS.1 hT.1 _ (hw l), fun P => ?_⟩
  have e1 := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ A' WW _ _ (X.ω' t) hW hθ X.rA'.s X.rA'.s X.rA'.B X.rA'.B
    X.rW.s X.rW.s X.rW.B X.rW.B x h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hx, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hh, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hx, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hh, Matrix.one_mul]) (X.f' t)
    (theta_of_alg hv.1 hv.2.theta hf) P).2
  have e2 := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ A' WW hv.1 hθ X.rA'.s X.rW.s X.rA'.B X.rW.B X.vac'
    hv.2.theta k c w hw P).1
  have ft := (GlobalTheory.FinTranslate.finite_translate D W.ψ W.θ A' WW hv.1 hθ X.vac' hv.2.theta).2
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker' thetaKO
  rw [e1, e, ← e2, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(ft (w l) (hw l)).2, Pi.smul_apply, smul_eq_mul]
end GlobalTheory.BotExpand
end
end
