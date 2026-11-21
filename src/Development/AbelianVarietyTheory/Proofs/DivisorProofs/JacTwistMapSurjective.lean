import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.TypeTwo.EndTwist

section General

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

def twistSubIso (ρ : Representation F G V) (χ : G →* Fˣ) :
    Subrepresentation ρ ≃o Subrepresentation (twist ρ χ) where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    show (χ g : F) • ρ g v ∈ S.toSubmodule
    exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
  invFun S := ⟨S.toSubmodule, fun g v hv => by
    have h := S.toSubmodule.smul_mem ((χ g)⁻¹ : Fˣ).val (S.apply_mem_toSubmodule g hv)
    have h2 : ((χ g)⁻¹ : Fˣ).val • (twist ρ χ g v) = ρ g v := by
      rw [twist_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rwa [h2] at h⟩
  left_inv S := rfl
  right_inv S := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_twist {ρ : Representation F G V} (h : ρ.IsIrreducible) (χ : G →* Fˣ) :
    (twist ρ χ).IsIrreducible :=
  (OrderIso.isSimpleOrder_iff (twistSubIso ρ χ)).1 h

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n a b V : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [AddCommGroup V] [Module ℂ V]

def pairChar (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) :
    GL a k × GL b k →* ℂˣ :=
  (detChar a μ).comp (MonoidHom.fst _ _) * (detChar b μ).comp (MonoidHom.snd _ _)

theorem pairChar_apply (μ : kˣ →* ℂˣ) (g : GL a k × GL b k) :
    pairChar a b μ g = μ (Matrix.GeneralLinearGroup.det g.1) * μ (Matrix.GeneralLinearGroup.det g.2) := rfl

end Local

end GlobalTheory.TypeTwo.EndTwist
