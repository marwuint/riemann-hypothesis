import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotallyIsotropicDimBoundsOddRank
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicStabilizerSplitPlaceInConjParabolics
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentUnipotentIntegralVanishSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentIntegralsPureTensorVanishOfLocal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.parabolic_and_constant_term

section Star

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem starFn_tensor (fa : ∀ w, GArch σ J w → ℂ) (ff : ∀ v, GLoc σ J v → ℂ) :
    starFn (tensor σ J fa ff) = tensor σ J (fun w => starFn (fa w)) (fun v => starFn (ff v)) := by
  funext g
  simp only [starFn, tensor, map_mul, map_prod, map_inv]
  congr 1
  exact MonoidHom.map_finprod_of_injective (starRingEnd ℂ).toMonoidHom (starRingEnd ℂ).injective _

theorem starFn_unitLoc (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) :
    starFn (unitLoc σ J L v) = unitLoc σ J L v := by
  funext g
  by_cases hg : g ∈ stabLoc σ J L v
  · simp [starFn, unitLoc, hg, Set.indicator_of_mem, inv_mem hg]
  · have : g⁻¹ ∉ stabLoc σ J L v := fun h => hg (by simpa using inv_mem h)
    simp [starFn, unitLoc, hg, this]

theorem isFinFamily_starFn {L : Submodule (𝓞 E) (Fin n → E)} {ff : ∀ v, GLoc σ J v → ℂ}
    (h : IsFinFamily σ J L ff) : IsFinFamily σ J L (fun v => starFn (ff v)) :=
  ⟨fun v => starFn_mem_SB (h.1 v), h.2.mono fun v hv => by simp only [hv, starFn_unitLoc]⟩

end Star

theorem inConjParabolic_mono {k : Type} [Field k] {r : ℕ} {H H' : Subgroup (GL (Fin r) k)} (h : H ≤ H') {a : ℕ}
    (h' : InConjParabolic H' a) : InConjParabolic H a :=
  let ⟨g, hg⟩ := h'; ⟨g, fun p hp => hg p (h hp)⟩

theorem parabolicAtSplitPlaces : ParabolicAtSplitPlaces := by
  intro D V hodd T 𝔉 hP
  let i : Fin (𝔉.k + 1) := ⟨1, Nat.succ_lt_succ hP⟩
  have hi : i ≠ 0 := Fin.ne_of_val_ne one_ne_zero
  have hW := 𝔉.isIsotropic hi
  obtain ⟨h0, h2⟩ := _root_.GlobalTheory.IsoDim.isotropic_dim_bounds D V hodd _ hW
  refine ⟨_, h0, h2, fun v => ?_⟩
  have hle : parAt 𝔉 (T.frame v) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v.1) (𝔉.X i)).map
      ((T.frame v).equiv : GLoc D.sp.cm.sig V.gram v.1 →* GL (Fin V.rank) (Fv D.host.F v.1)) :=
    Subgroup.map_mono (𝔉.par_le_parab _ _ i)
  obtain ⟨h3, h4⟩ := _root_.GlobalTheory.SplitStab.splitStab D V v.1 (T.frame v) _ hW
  exact ⟨inConjParabolic_mono hle h3, inConjParabolic_mono hle h4⟩

end GlobalTheory.Proof.parabolic_and_constant_term

end
