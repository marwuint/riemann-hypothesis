import Formalism.WachLatticeTwists.TorsionKernelSplitting.WachTwistSplitTheoremHZero

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

def StatRankLe : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Cs HV : Type) [AddCommGroup Cs] [Module O Cs] [AddCommGroup HV] [Module O HV]
    [Module (FractionRing O) HV] [IsScalarTower O (FractionRing O) HV]
    (jT : Cs →ₗ[O] HV) (Fs : Submodule O Cs) (Hf : Submodule (FractionRing O) HV),
    Module.Finite (FractionRing O) Hf →
    (∀ x ∈ Fs, jT x ∈ Hf) →
    (∀ x ∈ Fs, jT x = 0 → ∃ c : O, c ≠ 0 ∧ c • x = 0) →
    Module.finrank O Fs ≤ Module.finrank (FractionRing O) Hf

def StatKerTors : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (D : Type) [Group D]
    (T₂ V A Cs HV : Type) [AddCommGroup T₂] [Module O T₂] [AddCommGroup V] [Module O V]
    [AddCommGroup A] [Module O A] [AddCommGroup Cs] [Module O Cs] [AddCommGroup HV] [Module O HV]
    (ρ₂ : Representation O D T₂) (ρV : Representation O D V) (ρA : Representation O D A)
    (i : T₂ →ₗ[O] V) (q : V →ₗ[O] A) (Zc : Submodule O (D → T₂)) (cls : (D → T₂) → Cs)
    (Fs : Submodule O Cs) (clsV : (D → V) → HV) (jT : Cs →ₗ[O] HV),
    IsLatSeq ρ₂ ρV ρA i q → IsClassMap ρ₂ Zc cls Fs →
    (∀ z : A, ∃ c : O, c ≠ 0 ∧ c • z = 0) →
    (∀ a ∈ Zc, jT (cls a) = clsV (fun g => i (a g))) →
    (∀ a ∈ Zc, clsV (fun g => i (a g)) = 0 → (fun g => i (a g)) ∈ coB1 ρV) →
    ∀ x ∈ Fs, jT x = 0 → ∃ c : O, c ≠ 0 ∧ c • x = 0

end Formalism.RepresentationBoundsCohomology.JS
