import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBaseChangeQuotientOfMapMaximalIdeal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SelmerLevel

section Comp

variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {ι : Type} [Fintype ι]
  (b : Module.Basis ι O O')

structure Comp (A A' : Type) [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O' A'] where
  inc : A →+ A'
  p : ι → A' →+ A
  sum_p : ∀ x, ∑ a, b a • inc (p a x) = x
  p_inc : ∀ a c x, p a (c • inc x) = b.repr c a • x

def Comp.self : Comp b O O' where
  inc := (algebraMap O O').toAddMonoidHom
  p a := (b.coord a).toAddMonoidHom
  sum_p x := by
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Algebra.smul_def, mul_comm]
  p_inc a c x := by
    have : c • (algebraMap O O').toAddMonoidHom x = x • c := by simp [Algebra.smul_def, mul_comm]
    rw [this]; simp [mul_comm]

variable {b} {A A' : Type} [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O' A']

namespace Comp

variable (S : Comp b A A')

theorem ext_p {x y : A'} (h : ∀ a, S.p a x = S.p a y) : x = y := by
  rw [← S.sum_p x, ← S.sum_p y]; simp [h]

theorem p_inc' (a : ι) (x : A) : S.p a (S.inc x) = b.repr 1 a • x := by
  rw [← S.p_inc, one_smul]

theorem inc_smul (o : O) (x : A) : S.inc (o • x) = algebraMap O O' o • S.inc x := by
  refine S.ext_p fun a => ?_
  rw [S.p_inc', S.p_inc, Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply,
    smul_eq_mul, smul_smul, mul_comm]

include S in
theorem length_eq : Module.length O' A' = Module.length O' (O' ⊗[O] A) := by
  letI : Module O A' := Module.compHom A' (algebraMap O O')
  haveI : IsScalarTower O O' A' := ⟨fun o c x => by
    change (o • c) • x = algebraMap O O' o • c • x
    rw [Algebra.smul_def, mul_smul]⟩
  let f : A →ₗ[O] A' := { S.inc with map_smul' := S.inc_smul }
  let F : O' ⊗[O] A →ₗ[O'] A' := f.liftBaseChange O'
  have hF : ∀ c x, F (c ⊗ₜ x) = c • S.inc x := fun c x => LinearMap.liftBaseChange_tmul _ _ _ _
  have hl : ∀ t, ∑ a, b a ⊗ₜ[O] S.p a (F t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      simp only [hF, S.p_inc, ← TensorProduct.smul_tmul]
      rw [← TensorProduct.sum_tmul, b.sum_repr]
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]
  refine (LinearEquiv.ofBijective F ⟨fun s t h => ?_, fun x => ⟨∑ a, b a ⊗ₜ[O] S.p a x, ?_⟩⟩).length_eq.symm
  · rw [← hl s, ← hl t, h]
  · simp only [map_sum, hF, S.sum_p]

def pi (X : Type) : Comp b (X → A) (X → A') where
  inc := AddMonoidHom.compLeft S.inc X
  p a := AddMonoidHom.compLeft (S.p a) X
  sum_p x := by funext g; simp [S.sum_p]
  p_inc a c x := by funext g; simp [S.p_inc]

def Compat (N : Submodule O A) (N' : Submodule O' A') : Prop := ∀ x, x ∈ N' ↔ ∀ a, S.p a x ∈ N

variable {S}

theorem Compat.inc_mem {N : Submodule O A} {N' : Submodule O' A'} (h : S.Compat N N') {x : A}
    (hx : x ∈ N) : S.inc x ∈ N' :=
  (h _).2 fun a => by rw [S.p_inc']; exact N.smul_mem _ hx

def Compat.sub {N : Submodule O A} {N' : Submodule O' A'} (h : S.Compat N N') : Comp b N N' where
  inc := { toFun x := ⟨S.inc x, h.inc_mem x.2⟩
           map_zero' := Subtype.ext (map_zero _)
           map_add' x y := Subtype.ext (map_add _ _ _) }
  p a := { toFun x := ⟨S.p a x, (h _).1 x.2 a⟩
           map_zero' := Subtype.ext (map_zero _)
           map_add' x y := Subtype.ext (map_add _ _ _) }
  sum_p x := Subtype.ext (by simpa using S.sum_p x)
  p_inc a c x := Subtype.ext (S.p_inc a c x)

def Compat.quot {N : Submodule O A} {N' : Submodule O' A'} (h : S.Compat N N') :
    Comp b (A ⧸ N) (A' ⧸ N') where
  inc := QuotientAddGroup.map N.toAddSubgroup N'.toAddSubgroup S.inc fun _ hx => h.inc_mem hx
  p a := QuotientAddGroup.map N'.toAddSubgroup N.toAddSubgroup (S.p a) fun x hx => (h x).1 hx a
  sum_p x := by
    obtain ⟨x, rfl⟩ := N'.mkQ_surjective x
    conv_rhs => rw [← S.sum_p x, map_sum]
    rfl
  p_inc a c x := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    rw [← map_smul, ← S.p_inc]
    rfl

variable (S)

end Comp

end Comp

section Frac

variable {O O' : Type} [CommRing O] [IsDomain O] [CommRing O'] [IsDomain O'] [Algebra O O']
  [FaithfulSMul O O'] [Module.Finite O O'] {ι : Type} [Fintype ι] (b : Module.Basis ι O O')

attribute [local instance] FractionRing.liftAlgebra

def fracBasis : Module.Basis ι (FractionRing O) (FractionRing O') :=
  b.localizationLocalization (FractionRing O) (nonZeroDivisors O) (FractionRing O')

def fracComp : Comp b (FractionRing O) (FractionRing O') where
  inc := (algebraMap (FractionRing O) (FractionRing O')).toAddMonoidHom
  p a := ((fracBasis b).coord a).toAddMonoidHom
  sum_p x := by
    conv_rhs => rw [← (fracBasis b).sum_repr x]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Algebra.smul_def, mul_comm, fracBasis]
  p_inc a c x := by
    have : c • (algebraMap (FractionRing O) (FractionRing O')).toAddMonoidHom x =
        x • algebraMap O' (FractionRing O') c := by simp [Algebra.smul_def, mul_comm]
    rw [this]
    change (fracBasis b).repr (x • _) a = _
    rw [map_smul, Finsupp.smul_apply, fracBasis, Module.Basis.localizationLocalization_repr_algebraMap,
      Algebra.smul_def (b.repr c a), smul_eq_mul, mul_comm]

theorem fracComp_inc (x : FractionRing O) :
    (fracComp b).inc x = algebraMap (FractionRing O) (FractionRing O') x := rfl

theorem frac_compat : (fracComp b).Compat (LinearMap.range (Algebra.linearMap O (FractionRing O)))
    (LinearMap.range (Algebra.linearMap O' (FractionRing O'))) := by
  intro x
  constructor
  · rintro ⟨c, rfl⟩ a
    refine ⟨b.repr c a, ?_⟩
    have := (fracComp b).p_inc a c 1
    simpa [fracComp_inc, ← Algebra.algebraMap_eq_smul_one] using this.symm
  · intro h
    choose m hm using h
    rw [← (fracComp b).sum_p x]
    refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ⟨algebraMap O O' (m a), ?_⟩
    rw [← hm, fracComp_inc]
    simp [← IsScalarTower.algebraMap_apply]

open Formalism.MainNotions.BlochKatoReduction

def fracClasses {Γ O₀ : Type} [Group Γ] [TopologicalSpace Γ] [CommRing O₀] {O : Type} [CommRing O]
    [IsDomain O] (φ : O₀ →+* O) {r : ℕ} (ρ : Representation O Γ (Fin r → KmodO O)) {C : Type}
    (P : C → Prop) (Fr : C → Γ → Fin r → O₀ → O₀ → Prop) : Set (H1 ρ) :=
  {x | ∃ (z : Z1 ρ) (c : C) (y : Γ → Fin r → FractionRing O), P c ∧
    (∀ g a, ∃ n d : O₀, Fr c g a n d ∧
      algebraMap O (FractionRing O) (φ d) * y g a = algebraMap O (FractionRing O) (φ n)) ∧
    (∀ g a, (z : Γ → Fin r → KmodO O) g a = Submodule.Quotient.mk (y g a)) ∧
    x = Submodule.Quotient.mk z}

end Frac

section Main

open Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.GaloisCohomology

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

open Classical in

def bkG {O : Type} [CommRing O] [IsDomain O] (φ : X.O0 i →+* O) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule O (H1 ((twRep φ (X.rhoS i s) (chiS i s) 1).comp (DecV N v).subtype)) :=
  if hv : v ∈ placesOver D.host.E (X.l i) then
    Submodule.span O (fracClasses φ _
      (fun c => c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)))
      (fun c g a n d => IsFrac bkP i v hv (c ((bkP.br i v hv).e g) a) n d))
  else ⊥

def selG {O : Type} [CommRing O] [IsDomain O] (φ : X.O0 i →+* O)
    (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    Submodule O (H1 (twRep φ (X.rhoS i s) (chiS i s) 1)) :=
  SelAll _ N.plOm (bkCond _ N.plOm (X.l i) (Spl i ∪ ↑Q) (bkG bkP i s φ))

end Main

end GlobalTheory.SelmerLevel

end
