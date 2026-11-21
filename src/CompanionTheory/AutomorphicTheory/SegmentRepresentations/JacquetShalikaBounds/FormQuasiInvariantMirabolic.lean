import CompanionTheory.AutomorphicTheory.SegmentRepresentations.JacquetShalikaBounds.CMMul

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical
open scoped ValuativeRel

namespace CompanionTheory.JacquetShalikaLocal

def ForF (P : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F], Measure F → AddChar F ℂ → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure] (ψ : AddChar F ℂ), PsiOK ψ → P F μ ψ

def L2 : Prop := ForF fun F _ _ _ _ _ μ ψ => ∀ (k c c' : ℕ) (f : (Fin (k + 1) → F) → ℂ),
  (∀ x y, (∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ c' * t) → f (x + y) = f x) →
  (∀ h : GL (Fin (k + 1)) F, Div (c + 1) ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) - 1) →
    ∀ x, f ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) = f x) →
  ∀ g : GL (Fin (k + 1)) F, Div (c + 1) ((g⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) →
    ∫ x in (fun x => (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) '' lat F (k + 1) 0,
        ψ (-x (Fin.last k)) * f x ∂(Measure.pi fun _ => μ) =
      ∫ x in lat F (k + 1) (c + 1), ψ (-x (Fin.last k)) * f x ∂(Measure.pi fun _ => μ)

end CompanionTheory.JacquetShalikaLocal

end
