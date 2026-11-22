import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqMulOfRankAtStalk

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

variable {S S' : Scheme.{0}} {O : Type} [Ring O]

section Basic

variable {A A' A'' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj A'']
  [IsCommMonObj A'']

structure IsLin (ρ : RingAct A O) (ρ' : RingAct A' O) (f : A ⟶ A') : Prop where
  hom : IsMonHom f
  comm : ∀ a, ρ.act a ≫ f = f ≫ ρ'.act a

structure IsIsogDeg (f : A ⟶ A') (d : ℕ) : Prop where
  fin : IsFinite f.left
  flat : Flat f.left
  surj : Surjective f.left
  rank : ∀ y, f.left.finrank y = d

def KilledBy (ρ : RingAct A O) (𝔴 : Ideal O) {T : Over S} (x : T ⟶ A) : Prop :=
  ∀ a ∈ 𝔴, x ≫ ρ.act a = 1

theorem IsLin.id (ρ : RingAct A O) : IsLin ρ ρ (𝟙 A) := ⟨inferInstance, fun _ => by simp⟩

theorem IsLin.comp {ρ : RingAct A O} {ρ' : RingAct A' O} {ρ'' : RingAct A'' O} {f : A ⟶ A'} {g : A' ⟶ A''}
    (hf : IsLin ρ ρ' f) (hg : IsLin ρ' ρ'' g) : IsLin ρ ρ'' (f ≫ g) := by
  have := hf.hom
  have := hg.hom
  exact ⟨inferInstance, fun a => by rw [← Category.assoc, hf.comm, Category.assoc, hg.comm, Category.assoc]⟩

omit [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] in

theorem IsIsogDeg.of_isIso (f : A ⟶ A') [IsIso f] : IsIsogDeg f 1 := by
  have : IsIso f.left := inferInstanceAs (IsIso ((Over.forget S).map f))
  exact ⟨inferInstance, inferInstance, inferInstance, congrFun (Scheme.Hom.finrank_eq_one_of_isIso _)⟩

omit [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj A''] [IsCommMonObj A''] in

theorem IsIsogDeg.comp {f : A ⟶ A'} {g : A' ⟶ A''} {d e : ℕ} (hf : IsIsogDeg f d) (hg : IsIsogDeg g e) :
    IsIsogDeg (f ≫ g) (d * e) := by
  have := hf.fin; have := hf.flat; have := hf.surj
  have := hg.fin; have := hg.flat; have := hg.surj
  refine ⟨?_, ?_, ?_, fun y => ?_⟩
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left, FinrankComp.finrank_comp_of_const _ _ d hf.rank, hg.rank]

omit [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] in

theorem IsIsogDeg.epi {f : A ⟶ A'} {d : ℕ} (hf : IsIsogDeg f d) : Epi f := by
  have := hf.flat; have := hf.surj
  have : Epi f.left := Flat.epi_of_flat_of_surjective _
  exact Over.epi_of_epi_left f

omit [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] in

theorem IsIsogDeg.of_isPullback {C C' : Over S'} {f : A ⟶ A'} {g : C ⟶ C'} {d : ℕ} (hf : IsIsogDeg f d)
    {u : C.left ⟶ A.left} {v : C'.left ⟶ A'.left} (H : IsPullback u g.left f.left v) : IsIsogDeg g d := by
  have := hf.fin; have := hf.flat
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) H hf.fin,
    MorphismProperty.of_isPullback (P := @Flat) H hf.flat,
    MorphismProperty.of_isPullback (P := @Surjective) H hf.surj,
    fun y => (Scheme.Hom.finrank_of_isPullback _ _ _ _ H y).trans (hf.rank _)⟩

abbrev ker (f : A ⟶ A') : Over S := pullback f η[A']

omit [GrpObj A] [IsCommMonObj A] [IsCommMonObj A'] in

theorem IsIsogDeg.ker {f : A ⟶ A'} {d : ℕ} (hf : IsIsogDeg f d) : IsIsogDeg (toUnit (ker f)) d := by
  rw [toUnit_unique (toUnit _) (pullback.snd f η[A'])]
  exact hf.of_isPullback ((IsPullback.of_hasPullback f η[A']).map (Over.forget S))

theorem killedBy_span (ρ : RingAct A O) (s : Set O) {T : Over S} (x : T ⟶ A) :
    KilledBy ρ (Ideal.span s) x ↔ ∀ a ∈ s, x ≫ ρ.act a = 1 := by
  refine ⟨fun h a ha => h a (Ideal.subset_span ha), fun h a ha => ?_⟩
  have hadd : ∀ a b, x ≫ ρ.act (a + b) = (x ≫ ρ.act a) * (x ≫ ρ.act b) := fun a b => by
    rw [ρ.map_add]; exact MonObj.comp_mul x _ _
  induction ha using Submodule.span_induction with
  | mem a ha => exact h a ha
  | zero =>
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  | add a b _ _ ha hb => rw [hadd, ha, hb, _root_.mul_one]
  | smul c a _ ha =>
    have := ρ.hom c
    rw [smul_eq_mul, ρ.map_mul, ← Category.assoc, ha, MonObj.one_comp]

theorem comp_eq_one_iff_push {C C' : Over S'} [GrpObj C] [GrpObj C'] {f : S' ⟶ S} {u : C.left ⟶ A.left}
    {v : C'.left ⟶ A'.left} (hu : IsGrpPullback C A f u) (hv : IsGrpPullback C' A' f v) {g : A ⟶ A'} {g' : C ⟶ C'}
    (hg : g'.left ≫ v = u ≫ g.left) {T : Over S'} (x : T ⟶ C) :
    x ≫ g' = 1 ↔ pushHom hu T x ≫ g = 1 := by
  have e : pushHom hv T (x ≫ g') = pushHom hu T x ≫ g := Over.OverMorphism.ext (by
    change (x.left ≫ g'.left) ≫ v = (x.left ≫ u) ≫ g.left
    rw [Category.assoc, hg, Category.assoc])
  have inj : Function.Injective (pushHom hv T) := fun y z h => Over.OverMorphism.ext
    (hv.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  rw [← e, map_eq_one_iff _ inj]

end Basic

variable {A : Over S} [GrpObj A] [IsCommMonObj A]

structure Chain (ρ : RingAct A O) (𝔴 : Ideal O) (d n : ℕ) where

  B : Fin (n + 1) → Over S
  [grp : ∀ i, GrpObj (B i)]
  [comm : ∀ i, IsCommMonObj (B i)]
  ab : ∀ i, IsAbelianScheme (B i)

  act : ∀ i, RingAct (B i) O

  φ : ∀ i : Fin n, B i.castSucc ⟶ B i.succ
  φ_lin : ∀ i, IsLin (act _) (act _) (φ i)
  φ_deg : ∀ i, IsIsogDeg (φ i) d

  π : ∀ i, A ⟶ B i
  π_zero_lin : IsLin ρ (act 0) (π 0)
  π_zero_iso : IsIso (π 0)
  π_succ : ∀ i : Fin n, π i.succ = π i.castSucc ≫ φ i
  ker_last : ∀ (T : Over S) (x : T ⟶ A), x ≫ π (Fin.last n) = 1 ↔ KilledBy ρ 𝔴 x

attribute [instance] Chain.grp Chain.comm

namespace Chain

variable {ρ : RingAct A O} {𝔴 : Ideal O} {d n : ℕ} (C : Chain ρ 𝔴 d n)

theorem π_lin (i : Fin (n + 1)) : IsLin ρ (C.act i) (C.π i) := by
  induction i using Fin.induction with
  | zero => exact C.π_zero_lin
  | succ i ih => rw [C.π_succ]; exact ih.comp (C.φ_lin i)

theorem π_deg (i : Fin (n + 1)) : IsIsogDeg (C.π i) (d ^ (i : ℕ)) := by
  induction i using Fin.induction with
  | zero => have := C.π_zero_iso; exact IsIsogDeg.of_isIso _
  | succ i ih => rw [C.π_succ, Fin.val_succ, pow_succ]; exact ih.comp (C.φ_deg i)

theorem ker_mono {T : Over S} (x : T ⟶ A) {i j : Fin (n + 1)} (hij : i ≤ j) (h : x ≫ C.π i = 1) :
    x ≫ C.π j = 1 := by
  induction j using Fin.induction with
  | zero => obtain rfl := Fin.le_zero_iff.1 hij; exact h
  | succ j ih =>
    rcases hij.eq_or_lt with rfl | hlt
    · exact h
    · have := (C.φ_lin j).hom
      rw [C.π_succ, ← Category.assoc, ih (Fin.le_castSucc_iff.2 hlt), MonObj.one_comp]

theorem killedBy_of_π {T : Over S} (x : T ⟶ A) {i : Fin (n + 1)} (h : x ≫ C.π i = 1) : KilledBy ρ 𝔴 x :=
  (C.ker_last T x).1 (C.ker_mono x (Fin.le_last i) h)

theorem existsUnique_close (i : Fin (n + 1)) {a : O} (ha : a ∈ 𝔴) :
    ∃! g : C.B i ⟶ A, C.π i ≫ g = ρ.act a := by
  have h := C.π_deg i
  have := h.fin; have := h.flat; have := h.surj; have := h.epi
  have := (C.π_lin i).hom
  have := ρ.hom a
  obtain ⟨g, hg⟩ := AbelianQuotient.exists_desc (C.π i) (ρ.act a) fun W x y e => by
    have h1 : (x / y) ≫ C.π i = 1 := by rw [GrpObj.div_comp, e, div_self']
    have h2 := C.killedBy_of_π _ h1 a ha
    rwa [GrpObj.div_comp, div_eq_one] at h2
  exact ⟨g, hg, fun g' hg' => by rw [← cancel_epi (C.π i), hg, hg']⟩

def transport {A' : Over S} [GrpObj A'] [IsCommMonObj A'] {ρ' : RingAct A' O} (e : A' ≅ A) (he : IsLin ρ' ρ e.hom) :
    Chain ρ' 𝔴 d n where
  B := C.B
  ab := C.ab
  act := C.act
  φ := C.φ
  φ_lin := C.φ_lin
  φ_deg := C.φ_deg
  π i := e.hom ≫ C.π i
  π_zero_lin := he.comp C.π_zero_lin
  π_zero_iso := by have := C.π_zero_iso; infer_instance
  π_succ i := by rw [C.π_succ, Category.assoc]
  ker_last T x := by
    have := he.hom
    rw [← Category.assoc, C.ker_last]
    refine forall₂_congr fun a _ => ?_
    rw [Category.assoc, ← he.comm, ← Category.assoc, ← cancel_mono e.hom, MonObj.one_comp]

end Chain

structure ChainMap {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] {ρ' : RingAct A' O} {ρ : RingAct A O}
    {𝔴 : Ideal O} {d n : ℕ} (C' : Chain ρ' 𝔴 d n) (C : Chain ρ 𝔴 d n) (f : S' ⟶ S) (u : A'.left ⟶ A.left) where

  ψ : ∀ i, (C'.B i).left ⟶ (C.B i).left
  cart : ∀ i, IsGrpPullback (C'.B i) (C.B i) f (ψ i)
  act : ∀ i a, ((C'.act i).act a).left ≫ ψ i = ψ i ≫ ((C.act i).act a).left
  π_comm : ∀ i, (C'.π i).left ≫ ψ i = u ≫ (C.π i).left

namespace ChainMap

variable {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] {ρ' : RingAct A' O} {ρ : RingAct A O}
  {𝔴 : Ideal O} {d n : ℕ} {C' : Chain ρ' 𝔴 d n} {C : Chain ρ 𝔴 d n} {f : S' ⟶ S} {u : A'.left ⟶ A.left}

instance : Subsingleton (ChainMap C' C f u) := ⟨fun m m' => by
  have : m.ψ = m'.ψ := funext fun i => by
    have h := C'.π_deg i
    have := h.flat; have := h.surj
    have : Epi (C'.π i).left := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (C'.π i).left, m.π_comm, m'.π_comm]
  cases m; cases m'; cases this; rfl⟩

end ChainMap

end GlobalTheory.IwLevel
