import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

open MeasureTheory ValuativeRel Matrix Filter Topology
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip

namespace GlobalTheory.KSplit

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsSmU (χ : kˣ →* ℂˣ) : Prop := IsOpen (χ.ker : Set kˣ) ∧ ∀ x, ‖(χ x : ℂ)‖ = 1

def indSp (a a' : ℕ) (α β : kˣ →* ℂˣ) : Submodule ℂ (GL (Fin (a + a')) k → ℂ) where
  carrier := {f | (∀ (b : GL (Fin (a + a')) k) (A : GL (Fin a) k) (D : GL (Fin a') k) (N : Matrix (Fin a) (Fin a') k),
      b.val.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks A.val N 0 D.val → ∀ h, f (b * h) =
        (α (gdet A) : ℂ) * β (gdet D) * apow (gdet A) ((a' : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) * f h) ∧
    ∀ᶠ u in 𝓝 (1 : GL (Fin (a + a')) k), ∀ h, f (h * u) = f h}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun b A D N hb h => ?_, (h2.and h2').mono fun u hu h => ?_⟩
    · simp only [Pi.add_apply, h1 b A D N hb, h1' b A D N hb, mul_add]
    · simp only [Pi.add_apply, hu.1, hu.2]
  zero_mem' := ⟨fun _ _ _ _ _ _ => by simp, Eventually.of_forall fun _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨fun b A D N hb h => ?_, h2.mono fun u hu h => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, h1 b A D N hb]; ring
    · simp only [Pi.smul_apply, hu]

variable {a a' : ℕ} {z : ℂ} {ν α β : kˣ →* ℂˣ}

end Local

section Adelic

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def locMat {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GL (Fin n) (Fv F v)) :
    UA σ J →* GL (Fin n) (Fv F v) where
  toFun g := b⁻¹ * Matrix.GeneralLinearGroup.map (piW t) g.1 * b
  map_one' := by simp
  map_mul' g h := by simp [mul_assoc]

theorem locMat_val {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GL (Fin n) (Fv F v))
    (g : UA σ J) : (locMat t b g).val = (b⁻¹).val * (mat g).map (piW t) * b.val := rfl

end Adelic

end GlobalTheory.KSplit

end
