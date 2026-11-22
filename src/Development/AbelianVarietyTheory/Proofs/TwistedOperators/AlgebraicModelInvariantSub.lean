import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanMatricesTriple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KFinAlg

def tensDeg (F : Type) [Field F] [NumberField F] (P Q R S D : ℕ) : Submodule ℂ (GlobalTheory.RealLift.Tens F P Q R S) :=
  LinearMap.range (PiTensorProduct.map fun _ : InfinitePlace F =>
    (MvPolynomial.restrictTotalDegree (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ D).subtype)

theorem tensDeg_mono {F : Type} [Field F] [NumberField F] {P Q R S D D' : ℕ} (h : D ≤ D') :
    tensDeg F P Q R S D ≤ tensDeg F P Q R S D' := by
  have hi : MvPolynomial.restrictTotalDegree (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ D ≤
      MvPolynomial.restrictTotalDegree _ ℂ D' := fun x hx => by
    rw [MvPolynomial.mem_restrictTotalDegree] at hx ⊢; omega
  rintro _ ⟨t, rfl⟩
  refine ⟨PiTensorProduct.map (fun _ => Submodule.inclusion hi) t, ?_⟩
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  rfl

theorem exists_tensDeg {F : Type} [Field F] [NumberField F] {P Q R S : ℕ} (T : GlobalTheory.RealLift.Tens F P Q R S) :
    ∃ D, T ∈ tensDeg F P Q R S D := by
  classical
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    refine ⟨Finset.univ.sup fun w => (m w).totalDegree, r • PiTensorProduct.tprod ℂ (fun w =>
      (⟨m w, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (Finset.le_sup (f := fun w => (m w).totalDegree)
        (Finset.mem_univ w))⟩ : MvPolynomial.restrictTotalDegree _ ℂ _)), ?_⟩
    simp [PiTensorProduct.map_tprod]
  | add x y hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    exact ⟨max D₁ D₂, Submodule.add_mem _ (tensDeg_mono (le_max_left _ _) h₁) (tensDeg_mono (le_max_right _ _) h₂)⟩

theorem exp_stable {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (hU : GlobalTheory.RealLift.IsExp L U)
    (N : Submodule ℂ V) (hN : ∀ y ∈ N, L y ∈ N) : ∀ y ∈ N, U y ∈ N := by
  intro y hy
  by_contra hne
  obtain ⟨l, hl1, hl2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance
  have hpow : ∀ m : ℕ, (L ^ m) y ∈ N := by
    intro m
    induction m with
    | zero => simpa using hy
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hN _ ih
  have hz : ∀ m : ℕ, ((m.factorial : ℂ))⁻¹ * l ((L ^ m) y) = 0 := fun m => by
    have hm : l ((L ^ m) y) ∈ N.map l := Submodule.mem_map_of_mem (hpow m)
    rw [hl2, Submodule.mem_bot] at hm
    rw [hm, mul_zero]
  have h1 := hU y l
  simp only [hz] at h1
  exact hl1 (h1.unique hasSum_zero)

def pureL {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F]
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end GlobalTheory.SquareAgree.KFinAlg
