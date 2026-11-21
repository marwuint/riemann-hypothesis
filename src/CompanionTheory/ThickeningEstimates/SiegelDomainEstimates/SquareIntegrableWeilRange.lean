import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace CompanionTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (F) in

def rId (t : ℝ) : AF F := 1 + realAd F (Real.exp t - 1)

variable (σ) in

structure Frame {n : ℕ} (J : Matrix (Fin n) (Fin n) E) where

  r : ℕ

  x : Fin r → Fin n → E

  y : Fin r → Fin n → E

  a : (Fin r → ℝ) → UA σ J

structure Frame.IsGood {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (fr : Frame σ J) : Prop where
  xx : ∀ i j, form σ J (fr.x i) (fr.x j) = 0
  yy : ∀ i j, form σ J (fr.y i) (fr.y j) = 0
  xy : ∀ i j, form σ J (fr.x i) (fr.y j) = if i = j then 1 else 0
  aniso : ∀ u, (∀ i, form σ J u (fr.x i) = 0 ∧ form σ J u (fr.y i) = 0) → form σ J u u = 0 → u = 0
  add : ∀ s t, fr.a (s + t) = fr.a s * fr.a t
  cont : Continuous fr.a
  ax : ∀ t i, mat (fr.a t) *ᵥ incV F (fr.x i) = rId F (t i) • incV F (fr.x i)
  ay : ∀ t i, mat (fr.a t) *ᵥ incV F (fr.y i) = rId F (-t i) • incV F (fr.y i)
  a0 : ∀ t u, (∀ i, form σ J u (fr.x i) = 0 ∧ form σ J u (fr.y i) = 0) → mat (fr.a t) *ᵥ incV F u = incV F u

section Pair

variable {n d : ℕ}

scoped instance measAdPi {κ : Type} : MeasurableSpace (κ → AF F) := borel _

variable {X : Spc F E n} {W : Spc F E d}

end Pair

end CompanionTheory.ThKEst

end
