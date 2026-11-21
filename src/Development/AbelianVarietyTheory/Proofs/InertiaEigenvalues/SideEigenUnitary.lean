import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenvalueSystemSetFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationPointEigenSystemMem
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.EigPlace

theorem finite_and_mem (hstd : HeckeStdPlain) {D : D7} {M : MtFam D} (HT : HeckeTied D M) (av : AVTied D M)
    (T : NormalizedLocalCompatibility D M) (i : D.nd.Loc) (x : D.nd.X i) (Q : Finset (PlE D.host)) (hQ : D.nd.Q i = Q) :
    (EigSet (M (D.what₂.muTw (D.nd.w i)) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2)
        (D.what₂.places.resChar (D.nd.w i)) Q).Finite ∧
      ptSys D i x ∈ EigSet (M (D.what₂.muTw (D.nd.w i)) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2)
        (D.what₂.places.resChar (D.nd.w i)) Q := by
  subst hQ
  have hi : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · refine GlobalTheory.EigFinite.eigSet_finite hstd D _ _ _ _ _ (badPl D i) ?_ ?_
    · exact hypOutside_transport (D.nd.mu_w i) rfl (D.nd.j_range i).1 (D.nd.j_range i).2 _ _ _ (HT.J_hyp i)
    · intro v k s hg hc
      rw [T.Q_eq _ _ i hi] at hg
      exact genOutBad_of T _ _ i hi v k s hg hc
  · rw [D.nd.w_l i]
    exact GlobalTheory.FitHecke.mt_transport M (fun μ j m => ptSys D i x ∈ EigSet m (D.nd.l i) (D.nd.Q i)) (D.nd.mu_w i) rfl
      (D.nd.j_range i).1 (D.nd.j_range i).2 _ _ (GlobalTheory.PointEigen.ptSys_mem_eigSet D M av i x)

end GlobalTheory.EigPlace

end
