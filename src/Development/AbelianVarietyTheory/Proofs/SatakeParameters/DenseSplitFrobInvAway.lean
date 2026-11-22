import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobenius
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfUnramifiedOfInertiaDegEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatUnramifiedOverRealOfCmSubfield
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyResidueDegreeOnePrimeMovedByGalois

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.SplitAttUniq

private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem repIso_of_dense {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
    (r r' : G E Ω →* GL (Fin a) (Qbar l)) (hc : Continuous r) (hc' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r')
    (D : Set (G E Ω)) (hD : Dense D)
    (he : ∀ g ∈ D, (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly) :
    UpperTheory.V.Af.RepIso r r' := by
  have hcp : ∀ g : G E Ω, (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
      (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff i :=
      (contCoeff a i).comp (Units.continuous_val.comp hc)
    have h2 : Continuous fun g : G E Ω => (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff i :=
      (contCoeff a i).comp (Units.continuous_val.comp hc')
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    intro σ hσ
    simp only [he σ hσ]
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' hcp
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

end GlobalTheory.SplitAttUniq
