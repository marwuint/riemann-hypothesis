import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import ReciprocityTheory.GaloisValuations.Global

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.ZetaB

open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.NeedB GlobalTheory.KEdge

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

abbrev Om (X : Tower Ω ε) : Type := AlgebraicClosure X.K

attribute [local instance] algMdl

theorem isScalarTower_mdl_om (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
    @IsScalarTower (mdl X Γ' S) (lev X Γ') (Om X) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance] isScalarTower_mdl_om

open Classical in

def unitOf (X : Tower Ω ε) (a : X.K) : X.Kˣ := if h : a = 0 then 1 else Units.mk0 a h

def clsHat (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.K) : X.Khat l :=
  AdicCompletion.of (idl l) (X.Kl l) ((1 : ℤ_[l]) ⊗ₜ Additive.ofMul (unitOf X a))

def cR (l N : ℕ) (r₀ : ZMod l) : ℤ := (N : ℤ) * ((-r₀ * (N : ZMod l)⁻¹).val : ℤ)

def gR (l N : ℕ) (r₀ : ZMod l) : SL(2, ℤ) :=
  ⟨!![1, 0; cR l N r₀, 1], by simp [Matrix.det_fin_two]⟩

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in

theorem _root_.GlobalTheory.ZetaB.eval_clsHat (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (n : ℕ) (a : X.K) :
    AdicCompletion.eval (_root_.GlobalTheory.KZ.idl l) (X.Kl l) n
        (_root_.GlobalTheory.ZetaB.clsHat X l a) =
      X.cls l n (_root_.GlobalTheory.ZetaB.unitOf X a) := by
  unfold _root_.GlobalTheory.ZetaB.clsHat
  rw [AdicCompletion.eval_of]
  rfl

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in

theorem _root_.GlobalTheory.ZetaB.unitOf_val (X : _root_.GlobalTheory.KZ.Tower Ω ε) {a : X.K}
    (ha : a ≠ 0) : ((_root_.GlobalTheory.ZetaB.unitOf X a : (X.K)ˣ) : X.K) = a := by
  unfold _root_.GlobalTheory.ZetaB.unitOf
  rw [dif_neg ha]
  rfl

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in

theorem _root_.GlobalTheory.ZetaB.unitOf_zero (X : _root_.GlobalTheory.KZ.Tower Ω ε) :
    _root_.GlobalTheory.ZetaB.unitOf X 0 = 1 := by
  unfold _root_.GlobalTheory.ZetaB.unitOf
  rw [dif_pos rfl]

end GlobalTheory.ZetaB
