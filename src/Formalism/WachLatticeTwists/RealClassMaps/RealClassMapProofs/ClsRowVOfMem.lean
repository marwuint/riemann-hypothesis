import Formalism.WachLatticeTwists.RealClassMaps.StatClassMapReal

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG toH1Cocycles traceH1 transportCocycles)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

theorem kRowRange : StatKRowRange := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ G _ _ D M _ _ ρM u hu hopen
  have hdisc : DiscreteTopology (VT ⧸ D.T) :=
    QuotientAddGroup.discreteTopology (N := D.T.toAddSubgroup) hopen
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      refine ⟨transportCocycles (MulEquiv.refl G) u ρM D.ρA hu ⟨c.1, c.2.2⟩, ?_, rfl⟩
      have h1 : IsLocallyConstant c.1 := (IsLocallyConstant.iff_continuous _).2 c.2.1
      exact h1.comp u.symm
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : IsLocallyConstant (c : G → M) := hc
    have h3 : (fun g : G => u ((c : G → M) g)) ∈ Z1 D.ρA := by
      refine ⟨(hc'.comp u).continuous, fun a b => ?_⟩
      beta_reduce
      rw [c.2, map_add, hu]
    refine ⟨Submodule.Quotient.mk ⟨_, h3⟩, ?_⟩
    refine congrArg (Submodule.mkQ _) (Subtype.ext (funext fun g => ?_))
    change u.symm (u ((c : G → M) g)) = _
    rw [LinearEquiv.symm_apply_apply]

theorem resLC : StatResLC := by
  intro O G M _ _ _ _ _ ρ Dw
  rintro _ ⟨c, hc, rfl⟩
  have hc' : IsLocallyConstant (c : G → M) := hc
  refine ⟨restrictCocycles1 ρ Dw c, ?_, rfl⟩
  exact hc'.comp_continuous continuous_subtype_val

section
variable {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']

theorem clsRow_of_mem (D : LatData O Γ VT VT') {T₂ : Type} [AddCommGroup T₂] [Module O T₂] (v : T₂ ≃ₗ[O] D.T')
    (f : Γ → T₂) (h : (fun g => v (f g)) ∈ Z1 D.ρTl') : clsRow D v f = Submodule.Quotient.mk ⟨_, h⟩ :=
  dif_pos h

end

end Formalism.RepresentationBoundsCohomology.FIN
