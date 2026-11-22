import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormOneAddMulSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarAdditiveComplexLinearOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmooth
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExactFormsLeClosedForms

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CechDR GlobalTheory.CxForm GlobalTheory.CxPts
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ContDiff

namespace GlobalTheory.PD

section Smooth

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

abbrev dF (α : A.Fld) : A.Fld := A.dExt α

abbrev smForms : Subalgebra ℂ A.Fld := A.forms

abbrev dL : smForms A →ₗ[ℂ] smForms A := A.dForms

def filAt (n p : ℕ) (m : ℤ) : Submodule ℂ (Alt n) :=
  ⨅ T ∈ {T : Finset (Fin (n + n)) | ¬ ((T.card : ℤ) = m ∧ p ≤ (T.filter (·.val < n)).card)}, LinearMap.ker ((bas n).coord T)

def smCx (p : ℕ) : Cx ℂ (smForms A) :=
  ⟨fun m => ⨅ x : A.Pt, (filAt n p m).comap ((LinearMap.proj x : A.Fld →ₗ[ℂ] Alt n) ∘ₗ (smForms A).val.toLinearMap), dL A⟩

abbrev HSm (m : ℤ) : Type := (smCx A 0).H m

structure FormOn (S : Set M) (α : A.Fld) : Prop where
  smooth : ∀ i T, ContDiffOn ℝ ∞ (fun v => (bas n).repr (A.loc α i v) T) ((A.e i).target ∩ (A.e i).symm ⁻¹' S)
  compat : ∀ x x' : A.Pt, x.pt ∈ S → x.pt = x'.pt → α x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (α x')

variable {ι : Type} [LinearOrder ι]

def Rep (S : Finset ι → Set M) (g : Finset ι → A.Fld) (α : A.Fld) : Prop :=
  ∃ y : Finset ι → A.Fld, y ∅ = 0 ∧ (∀ s, FormOn A (S s) (y s)) ∧ ∀ s, s.Nonempty → ∀ x : A.Pt, x.pt ∈ S s →
    g s x = const α s x + GlobalTheory.DI.delta y s x + (-1 : ℤ) ^ s.card • dF A (y s) x

end Smooth

section Scheme

variable {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ)

variable [IsIntegral X]

@[reducible] def ffAlg : Algebra k X.functionField :=
  ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra

variable [Algebra k X.functionField]

omit σ in

structure IsAffCover {ι : Type} (U : ι → X.Opens) (B : Finset ι → Subalgebra k X.functionField) : Prop where
  alg : algebraMap k X.functionField = @algebraMap k X.functionField _ _ (ffAlg p)
  affine : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (I.inf U)
  cover : iSup U = ⊤
  ne : ∀ I : Finset ι, genericPoint X ∈ I.inf U
  ring : ∀ I : Finset ι, I.Nonempty → ∀ y, y ∈ B I ↔ ∃ f : Γ(X, I.inf U), (X.presheaf.germ (I.inf U) (genericPoint X) (ne I)).hom f = y

end Scheme

section Compare

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem mem_filAt_iff {p : ℕ} {m : ℤ} {a : Alt n} :
    a ∈ filAt n p m ↔ ∀ T, (bas n).repr a T ≠ 0 → (T.card : ℤ) = m ∧ p ≤ holCount T := by
  simp only [filAt, Submodule.mem_iInf, LinearMap.mem_ker, Set.mem_setOf_eq, Module.Basis.coord_apply, holCount]
  exact forall_congr' fun T => not_imp_comm

theorem mem_filAt_nat {p k : ℕ} {a : Alt n} : a ∈ filAt n p k ↔ HasDeg k a ∧ a ∈ holGe n p := by
  rw [mem_filAt_iff, mem_holGe_iff]
  exact ⟨fun h => ⟨fun T hT => by exact_mod_cast (h T hT).1, fun T hT => (h T hT).2⟩,
    fun h T hT => ⟨by exact_mod_cast h.1 T hT, h.2 T hT⟩⟩

variable {A}

theorem mem_smCx_C {p : ℕ} {m : ℤ} {α : smForms A} : α ∈ (smCx A p).C m ↔ ∀ x, α.1 x ∈ filAt n p m := by
  simp only [smCx, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem mem_smCx_C_nat {p k : ℕ} {α : smForms A} : α ∈ (smCx A p).C k ↔ A.IsDeg k α ∧ A.TypeGe p α := by
  rw [mem_smCx_C, HolAtlas.typeGe_iff]
  simp only [mem_filAt_nat]
  exact forall_and

theorem mem_smCx_Z_nat {p k : ℕ} {α : smForms A} : α ∈ (smCx A p).Z k ↔ α.1 ∈ A.closedForms k ∧ A.TypeGe p α := by
  rw [Cx.Z, Submodule.mem_inf, mem_smCx_C_nat, LinearMap.mem_ker, HolAtlas.mem_closedForms, Subtype.ext_iff]
  exact ⟨fun h => ⟨⟨α.2, h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.2.1, h.2⟩, h.1.2.2⟩⟩

variable (A)

def zEquiv (k : ℕ) : (smCx A 0).Z k ≃ₗ[ℂ] A.closedForms k where
  toFun α := ⟨α.1.1, (mem_smCx_Z_nat.1 α.2).1⟩
  invFun α := ⟨⟨α.1, α.2.1⟩, mem_smCx_Z_nat.2 ⟨α.2, fun _ _ _ => Nat.zero_le _⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem coe_zEquiv (k : ℕ) (α : (smCx A 0).Z k) : (zEquiv A k α : A.Fld) = α.1.1 := rfl

end Compare

end GlobalTheory.PD
