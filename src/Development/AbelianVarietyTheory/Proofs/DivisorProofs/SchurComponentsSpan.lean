import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeKeepsAndCommutes

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincipalDecomp

open GlobalTheory.SphericalOps GlobalTheory.HeckeAdjoint GlobalTheory.HeckeOrthSum

theorem mult_le_of_parts {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {M : DSModel V S} {J : Subgroup (GA D V)}
    {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure) (hF : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hS : SchurMult θ M (J : Set (GA D V)) χ μ 𝓕) [FiniteDimensional ℂ (Mult θ M (J : Set (GA D V)) χ)]
    (hK : ∀ P d R, Hecke₂ V (J : Set (GA D V)) χ Sb P d R →
      ∀ T ∈ Mult θ M (J : Set (GA D V)) χ, heckeOn M R T ∈ Mult θ M (J : Set (GA D V)) χ)
    (Z : Submodule ℂ (MMap M))
    (hZ : ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      (∀ P d, (¬ ∃ R, Hecke₂ V (J : Set (GA D V)) χ Sb P d R) → c P d = 0) →
        partFull θ M (J : Set (GA D V)) χ Sb c ≤ Z) :
    Mult θ M (J : Set (GA D V)) χ ≤ Z := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.SchurConst.ipM_posDef D θ V S M _ χ μ 𝓕 hθ hμ hF hS (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  have hpos : IsPosOn (Mult θ M (J : Set (GA D V)) χ) (ipM M μ 𝓕) :=
    ⟨fun x hx y hy z hz c => (h1 x hx y hy z hz c).1, fun x hx y hy => (h1 x hx y hy y hy 0).2, fun x hx => h2 x hx⟩
  refine hpos.le_iSup_eigen
    (I := {x : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D V) //
      Hecke₂ V (J : Set (GA D V)) χ Sb x.1 x.2.1 x.2.2})
    (fun i => heckeOn M i.1.2.2) (fun i => hK _ _ _ i.2) (fun i k T hT => ?_) ?_ Z ?_
  · rw [GlobalTheory.MultMem.mem_mult_iff] at hT
    exact MultilinearMap.ext fun v => comm_heckeLin (realUnif D _) i.2 k.2 (hT.lev v)
  · rintro ⟨⟨P, d, R⟩, hR⟩
    obtain ⟨R', hR', -⟩ := exists_dual (realUnif D P) hR
    exact ⟨⟨(P, dualLab d, R'), hR'⟩, fun T hT T' hT' =>
      ipM_heckeOn_dualLab D V S θ M J χ Sb μ 𝓕 hθ hμ hF hS P d R R' hR hR' T hT T' hT' (hK _ _ _ hR T hT)
        (hK _ _ _ hR' T' hT')⟩
  · intro x T hT hx
    let c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ := fun P d =>
      if h : ∃ R, Hecke₂ V (J : Set (GA D V)) χ Sb P d R then x ⟨(P, d, h.choose), h.choose_spec⟩ else 0
    refine hZ c (fun P d h => dif_neg h) ((mem_partFull ..).2 ⟨hT, fun P d R hR v => ?_⟩)
    have h : ∃ R, Hecke₂ V (J : Set (GA D V)) χ Sb P d R := ⟨R, hR⟩
    rw [labelUnique (realUnif D) P d R h.choose hR h.choose_spec (T v) (((GlobalTheory.MultMem.mem_mult_iff ..).1 hT).lev v)]
    simp only [c, dif_pos h]
    exact congrArg (fun U : MMap M => U v) (hx ⟨(P, d, h.choose), h.choose_spec⟩)

end GlobalTheory.PrincipalDecomp

end
