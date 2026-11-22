import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorLeftPartialPure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorRightPartialPureStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblEval

section Alg

variable {A : Type} {κ κ₁ κ₂ κ' κ₁' κ₂' : Type}

theorem partL_congr {T T' : ((κ → A) → ℂ) → (κ₁ → A) → ℂ} {Φ : (κ ⊕ κ' → A) → ℂ}
    (h : ∀ b : κ' → A, T (fun x => Φ (Sum.elim x b)) = T' (fun x => Φ (Sum.elim x b))) : partL T Φ = partL T' Φ := by
  funext y; simp only [partL, h]

theorem partR_congr {T T' : ((κ' → A) → ℂ) → (κ₁' → A) → ℂ} {Φ : (κ ⊕ κ' → A) → ℂ}
    (h : ∀ a : κ → A, T (fun x => Φ (Sum.elim a x)) = T' (fun x => Φ (Sum.elim a x))) : partR T Φ = partR T' Φ := by
  funext y; simp only [partR, h]

end Alg

section Heis

variable {R : Type} [CommRing R] [Invertible (2 : R)]

variable {κ : Type} [Fintype κ] (ψ : AddChar R ℂ) (hψ : ∀ t, ‖ψ t‖ = 1)
include hψ

theorem conj_psi (t : R) : starRingEnd ℂ (ψ t) = ψ⁻¹ t := by
  rw [AddChar.inv_apply, AddChar.map_neg_eq_inv]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ t]
  norm_num

end Heis

section Glue

variable {A : Type} {κ κ₁ κ' κ₁' : Type}

end Glue

section Rho

variable {R : Type} [CommRing R] [Invertible (2 : R)] {Wt : Type} [AddCommGroup Wt] [Module R Wt] {Bf : Wt → Wt → R}
  {κ κ₁ κ' κ₁' : Type} [Fintype κ] [Fintype κ']

end Rho

section Main

variable {F : Type} [Field F] [NumberField F]

theorem sliceL_mem {κ κ' : Type} [Fintype κ] [Fintype κ'] {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ'))
    (b : κ' → AF F) : (fun x => Φ (Sum.elim x b)) ∈ schA F κ := by
  have e1 : (fun x => Φ (Sum.elim x b)) = fun x => Φ (GlobalTheory.ThK.Adapt.glue (Equiv.sumComm κ κ') b x) :=
    funext fun x => congrArg Φ (funext fun k => by cases k <;> rfl)
  rw [e1]
  exact GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.sumComm κ κ') b hΦ

theorem sliceR_mem {κ κ' : Type} [Fintype κ] [Fintype κ'] {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ'))
    (a : κ → AF F) : (fun x => Φ (Sum.elim a x)) ∈ schA F κ' :=
  GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.refl (κ ⊕ κ')) a hΦ

variable {κ κ₁ κ' κ₁' : Type} [Fintype κ] [Fintype κ₁] [Fintype κ'] [Fintype κ₁']

theorem partL_mem (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ) (he : IsLocOp e) :
    ∀ Φ ∈ schA F (κ ⊕ κ'), partL e Φ ∈ schA F (κ₁ ⊕ κ') := by
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.DblEval.PartLStr.exists_partL_pureA (κ' := κ') e he
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨g₁, hg₁, h1⟩ := hP g hg
    rw [h1 f]
    exact Submodule.subset_span ⟨P f, g₁, hg₁, rfl⟩
  | zero => show partLₗ e 0 ∈ _; rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => show partLₗ e (x + y) ∈ _; rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => show partLₗ e (c • x) ∈ _; rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem partR_mem (e : ((κ' → AF F) → ℂ) →ₗ[ℂ] (κ₁' → AF F) → ℂ) (he : IsLocOp e) :
    ∀ Φ ∈ schA F (κ ⊕ κ'), partR e Φ ∈ schA F (κ ⊕ κ₁') := by
  obtain ⟨P, hP⟩ := GlobalTheory.T.local_operator_right_partial_pure (κ := κ) e he
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨g₁, hg₁, h1⟩ := hP g hg
    rw [h1 f]
    exact Submodule.subset_span ⟨P f, g₁, hg₁, rfl⟩
  | zero => show partRₗ e 0 ∈ _; rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => show partRₗ e (x + y) ∈ _; rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => show partRₗ e (c • x) ∈ _; rw [map_smul]; exact Submodule.smul_mem _ c hx

end Main

section Ev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end Ev

end GlobalTheory.DblEval
