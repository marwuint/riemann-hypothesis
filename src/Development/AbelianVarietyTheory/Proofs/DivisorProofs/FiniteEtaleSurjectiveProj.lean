import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftZero
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.Et.TrivTors

noncomputable section

namespace GlobalTheory.Et.TrivTors

def sigmaFinSuccIso (V : Scheme.{0}) (k : ℕ) :
    (∐ fun _ : Fin (k + 1) => V) ≅ V ⨿ (∐ fun _ : Fin k => V) where
  hom := Sigma.desc (Fin.cases coprod.inl fun i => Sigma.ι (fun _ : Fin k => V) i ≫ coprod.inr)
  inv := coprod.desc (Sigma.ι (fun _ : Fin (k + 1) => V) 0)
    (Sigma.desc fun i => Sigma.ι (fun _ : Fin (k + 1) => V) i.succ)
  hom_inv_id := by
    ext i
    induction i using Fin.cases
    · simp only [Fin.cases_zero, Sigma.ι_desc_assoc]
      exact coprod.inl_desc _ _
    · simp only [Fin.cases_succ, Sigma.ι_desc_assoc, Category.assoc, Category.comp_id]
      erw [coprod.inr_desc, Sigma.ι_desc]
  inv_hom_id := by
    apply coprod.hom_ext
    · erw [coprod.inl_desc_assoc, Sigma.ι_desc]
      simp
    · erw [coprod.inr_desc_assoc]
      ext i
      simp

theorem sigmaFinSuccIso_hom_desc (V : Scheme.{0}) (k : ℕ) :
    (sigmaFinSuccIso V k).hom ≫ coprod.desc (𝟙 V) (Sigma.desc fun _ : Fin k => 𝟙 V) =
      Sigma.desc fun _ : Fin (k + 1) => 𝟙 V := by
  ext i
  induction i using Fin.cases
  · simp only [sigmaFinSuccIso, Sigma.ι_desc_assoc, Fin.cases_zero, Sigma.ι_desc]
    exact coprod.inl_desc _ _
  · simp only [sigmaFinSuccIso, Sigma.ι_desc_assoc, Fin.cases_succ, Sigma.ι_desc, Category.assoc]
    erw [coprod.inr_desc, Sigma.ι_desc]

theorem isFinite_sigmaDesc_fin (V : Scheme.{0}) : ∀ k : ℕ, IsFinite (Sigma.desc fun _ : Fin k => 𝟙 V)
  | 0 => by
    have : IsEmpty (∐ fun _ : Fin 0 => V : Scheme.{0}) := by
      refine ⟨fun x => ?_⟩
      obtain ⟨i, _, _⟩ := (sigmaOpenCover fun _ : Fin 0 => V).exists_eq x
      exact i.elim0
    infer_instance
  | k + 1 => by
    have := isFinite_sigmaDesc_fin V k
    rw [← sigmaFinSuccIso_hom_desc]
    infer_instance

end GlobalTheory.Et.TrivTors
