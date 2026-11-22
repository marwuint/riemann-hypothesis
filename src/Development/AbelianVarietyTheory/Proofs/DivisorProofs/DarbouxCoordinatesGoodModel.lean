import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxCoordinatesCompareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterAlmostUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForLeviMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForWeylElement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem spAct_mul {R : Type} [CommRing R] [Algebra F R] (G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) :
    spAct (G * G') w = spAct G (spAct G' w) := by
  have h : Sum.elim (spAct G' w).1 (spAct G' w).2 = G'.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2 := by
    funext i; cases i <;> rfl
  conv_rhs => rw [spAct, h]
  simp only [spAct, Matrix.map_mul (f := algebraMap F R), Matrix.mulVec_mulVec]

variable [NumberField F]

theorem locCo_eq {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} (c₁ c₂ : Darboux B κ)
    (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (h : ∀ w, c₂.e w = spAct G (c₁.e w)) (v : Pl F) (γ : W) :
    GlobalTheory.LatVac.locCo c₂ v γ = spAct G (GlobalTheory.LatVac.locCo c₁ v γ) := by
  have key : ∀ (x : κ ⊕ κ → AF F) (i : κ ⊕ κ), evFin F v ((G.map (algebraMap F (AF F)) *ᵥ x) i) =
      (G.map (algebraMap F (Fv F v)) *ᵥ fun j => evFin F v (x j)) i := by
    intro x i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
  have hs : ∀ a b : κ → AF F, (fun j => evFin F v (Sum.elim a b j)) =
      Sum.elim (fun k => evFin F v (a k)) (fun k => evFin F v (b k)) := by
    intro a b; funext j; cases j <;> rfl
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h, spAct, key, hs]

theorem acts_unique' (v : Pl F) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0)
    (hR : Rest (evFin F v) φ R) {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  have e := (h₁ R hR).symm.trans (h₂ R hR)
  funext t
  have h := congrFun e (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hx : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    have := hR.1 0 (fun i => GlobalTheory.LatVac.liftV v (t i))
      (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hx] at h
  exact mul_right_cancel₀ hR0 h

end GlobalTheory.SympChange
