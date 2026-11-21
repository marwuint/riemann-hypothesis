import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaDistributionSumProductFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAdeleE
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot

noncomputable section

namespace GlobalTheory.DblBox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

def rIdx (n d : ℕ) : (Fin n × Fin d) ⊕ (Fin n × Fin d) ≃ Fin (n + n) × Fin d :=
  (Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))

@[simp] theorem rIdx_inl (p : Fin n × Fin d) : rIdx n d (.inl p) = (finSumFinEquiv (.inl p.1), p.2) := rfl

@[simp] theorem rIdx_inr (p : Fin n × Fin d) : rIdx n d (.inr p) = (finSumFinEquiv (.inr p.1), p.2) := rfl

def reix {R κ κ' : Type} (e : κ ≃ κ') : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ' → R) → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (Equiv.arrowCongr e (Equiv.refl R)).symm

theorem reix_apply {R κ κ' : Type} (e : κ ≃ κ') (φ : (κ → R) → ℂ) (x : κ' → R) : reix e φ x = φ (x ∘ e) := rfl

theorem reix_symm {R κ κ' : Type} (e : κ ≃ κ') : (reix (R := R) e).symm = reix e.symm := rfl

end GlobalTheory.DblBox

end
