import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeSpacesOrthogonalOfClassSumInner
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIsotypicInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPairThetaLowest
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRank
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinTypRowsExistsIsLocSAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsLocS
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section

namespace GlobalTheory.LiftRefIrr

theorem exists_ne_of_mem_iSup' {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Sort*} (p : ι → Submodule ℂ M)
    (ℓ : M →+ ℂ) {x : M} (hx : x ∈ ⨆ i, p i) (h : ℓ x ≠ 0) : ∃ i, ∃ y ∈ p i, ℓ y ≠ 0 := by
  by_contra H
  push_neg at H
  exact h (Submodule.iSup_induction p (motive := fun z => ℓ z = 0) hx (fun i y hy => H i y hy) (map_zero ℓ)
    (fun a b ha hb => by rw [map_add, ha, hb, add_zero]))

theorem exists_irr_pair {D : D7} {μ : D.what₂.Tup} {j : ℕ} (Mr : MtReal D μ j) (x : D.what₂.Mt μ j) (hx : x ≠ 0) :
    ∃ (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)) (_ : NG.IsIrrRep Mr.wt.ρ S),
      ∃ F ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, inner ℂ F x ≠ 0 := by
  obtain ⟨-, ι, -, S, hirr, -, -, -, -, hsum⟩ := _root_.GlobalTheory.CompRed.typeSp_decomp D.host.E D.R.nV Mr.wt Mr.J Mr.χ Mr.J_open
  let p : ι → Submodule ℂ (D.what₂.Mt μ j) :=
    fun i => (NG.isoTyp Mr.wt.ρ (S i) ⊓ NG.TypeSp Mr.wt.ρ Mr.J Mr.χ).comap Mr.real
  have htop : (⨆ i, p i) = ⊤ := by
    apply Submodule.map_injective_of_injective Mr.real_inj
    rw [Submodule.map_iSup, Submodule.map_top, Mr.real_range]
    conv_rhs => rw [← hsum]
    refine iSup_congr fun i => ?_
    show Submodule.map Mr.real (Submodule.comap Mr.real _) = _
    rw [Submodule.map_comap_eq, Mr.real_range]
    exact inf_eq_right.2 inf_le_right
  have hxm : x ∈ ⨆ i, p i := htop ▸ Submodule.mem_top
  let ℓ : D.what₂.Mt μ j →+ ℂ := AddMonoidHom.mk' (fun F => inner ℂ F x) (fun a b => inner_add_left a b x)
  obtain ⟨i, F, hF, hne⟩ := exists_ne_of_mem_iSup' p ℓ hxm (by
    show inner ℂ x x ≠ 0
    exact inner_self_ne_zero.2 hx)
  exact ⟨S i, hirr i, F, (Submodule.mem_inf.1 hF).1, hne⟩

end GlobalTheory.LiftRefIrr

end
