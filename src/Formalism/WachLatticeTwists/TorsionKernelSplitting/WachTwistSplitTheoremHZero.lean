import Formalism.WachLatticeTwists.TorsionKernelSplitting.Statement

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

def IsClassMap {O D T₂ Cs : Type*} [CommRing O] [Group D] [AddCommGroup T₂] [Module O T₂]
    [AddCommGroup Cs] [Module O Cs] (ρ₂ : Representation O D T₂) (Zc : Submodule O (D → T₂))
    (cls : (D → T₂) → Cs) (Fs : Submodule O Cs) : Prop :=
  (∀ a ∈ Zc, ∀ b ∈ Zc, cls (a + b) = cls a + cls b) ∧
  (∀ (c : O), ∀ a ∈ Zc, cls (c • a) = c • cls a) ∧
  (∀ a ∈ Zc, cls a = 0 ↔ a ∈ coB1 ρ₂) ∧
  (∀ x ∈ Fs, ∃ a ∈ Zc, x = cls a)

def IsLatSeq {O D T₂ V A : Type*} [CommRing O] [Group D] [AddCommGroup T₂] [Module O T₂]
    [AddCommGroup V] [Module O V] [AddCommGroup A] [Module O A]
    (ρ₂ : Representation O D T₂) (ρV : Representation O D V) (ρA : Representation O D A)
    (i : T₂ →ₗ[O] V) (q : V →ₗ[O] A) : Prop :=
  Function.Injective i ∧ (∀ v, q v = 0 ↔ v ∈ LinearMap.range i) ∧
  IsEquivMap ρ₂ ρV i ∧ IsEquivMap ρV ρA q

def TorsionLeHZero : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (D : Type) [Group D]
    (T₂ V A Cs : Type) [AddCommGroup T₂] [Module O T₂] [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    [AddCommGroup A] [Module O A] [AddCommGroup Cs] [Module O Cs]
    (ρ₂ : Representation O D T₂) (ρV : Representation O D V) (ρA : Representation O D A)
    (i : T₂ →ₗ[O] V) (q : V →ₗ[O] A) (Zc : Submodule O (D → T₂)) (cls : (D → T₂) → Cs)
    (Fs : Submodule O Cs),
    IsLatSeq ρ₂ ρV ρA i q → IsClassMap ρ₂ Zc cls Fs →
    Module.length O (Submodule.torsion O Fs) ≤ Module.length O (LinearMap.ker (coD0 ρA))

def StatFinSub : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Cs : Type) [AddCommGroup Cs] [Module O Cs] (Fs : Submodule O Cs),
    Module.Finite O Cs → Module.Finite O Fs

end Formalism.RepresentationBoundsCohomology.JS
