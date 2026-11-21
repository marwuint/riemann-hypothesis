import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Divisors.MemStdLatticeIffIntegralCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFiniteTypeIndexOfRowsPos
import Formalism.LocalToGlobal.IndefiniteReal.RealRecPins

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.MainNotions.N IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NJoin.Inh

section Weight

variable {D : D7}

theorem rat_unit {V : HSp D} (hg : V.gram = 1) (h : Formalism.AUTREP.GAf D.host.E V.rank) :
    h ∈ ReciprocityTheory.Aut.GQ D.host.E V.rank ↔
      ∃ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V ((GlobalTheory.StdFrameModel.unitPsi hg).ψ h) := by
  have hfin : finHom V ((GlobalTheory.StdFrameModel.unitPsi hg).ψ h) = Formalism.UG.bc (GlobalTheory.StdFrameModel.sw D).symm.toRingHom h.1 :=
    (GlobalTheory.StdFrameModel.exists_lift hg h).choose_spec.2
  have hU : ∀ x : GL (Fin V.rank) D.host.E, x ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank ↔
      x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
    intro x
    change x.1 * ReciprocityTheory.Aut.conjT _ x.1 = 1 ↔ Formalism.UG.cT _ x.1 * V.gram * x.1 = V.gram
    rw [hg, Matrix.mul_one, mul_eq_one_comm]
    rfl
  rw [hfin]
  constructor
  · rintro ⟨x, hx, e⟩
    have hx' := (hU x).1 hx
    have hm : Formalism.UG.bc (incA D) x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
      have h0 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1 * V.gram * x.1 = V.gram := hx'
      have h2 := congrArg (fun M => Matrix.map M (incA D)) h0
      simp only [Matrix.map_mul] at h2
      exact h2
    refine ⟨⟨_, hm⟩, ⟨x, hx', rfl⟩, ?_⟩
    have e' : h.1 = _ := e.symm
    rw [e']
    ext i j
    change (sndA D.host.F 1) ⊗ₜ[D.host.F] (x.1 i j) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x.1 i j)
    rw [map_one]
  · rintro ⟨γ, ⟨x, hx, e⟩, e2⟩
    refine ⟨x, (hU x).2 hx, ?_⟩
    ext i j
    have e3 := congrArg (fun g : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.1 i j) e2
    have e4 : (finHom V γ).1 i j = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x.1 i j) := by
      have e' : γ.1 = _ := e.symm
      change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (γ.1.1 i j) = _
      rw [e']
      change (sndA D.host.F 1) ⊗ₜ[D.host.F] (x.1 i j) = _
      rw [map_one]
    simp only [e4] at e3
    apply (GlobalTheory.StdFrameModel.sw D).symm.injective
    exact e3

variable {V : HSp D} (c : CoefA V)

end Weight

end GlobalTheory.NJoin.Inh

end
