import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.WhittakerModelGL2

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.LFS

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

instance mGL2 : MeasurableSpace (GL (Fin 2) F) := borel _
instance bGL2 : BorelSpace (GL (Fin 2) F) := ⟨rfl⟩

def vol2 (ψ : AddChar F Circle) : Measure (Fin 2 → F) := Measure.pi fun _ => selfDualMeasure ψ

def hG (ψ : AddChar F Circle) : Measure (GL (Fin 2) F) :=
  Measures.haarGL F 2 (Measure.pi fun _ : Fin 2 × Fin 2 => selfDualMeasure ψ)

structure Per (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (W : GL (Fin 3) F → ℂ) : Prop where
  psi : ∀ x y z g, W (uni x y z * g) = (ψ (x + z) : ℂ) * W g
  cen : ∀ (a : Fˣ) g, W (dg a a a * g) = W g
  smooth : ∃ U : OpenSubgroup (GL (Fin 3) F), ∀ g, ∀ u ∈ U, W (g * u) = W g
  gauge : ∃ (C B : ℝ) (T : ℕ), ∀ (a b : Fˣ), ∀ k ∈ GLnLocal.integralGL F 3,
    ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((modulus (a : F) : ℝ) * modulus (b : F)) ^ T ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B ∧ (modulus (b : F) : ℝ) ≤ B)
  int : ∀ s : ℂ, 1 / 4 < s.re → Integrable (zF W 1 s) (multHaar F)
  int' : ∀ s : ℂ, s.re < 3 / 4 → Integrable (zF' W 1 s) ((multHaar F).prod (selfDualMeasure ψ))
  fe : ∀ c, IsUnit1 c → ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 →
    ∫ p, zF' W c s p ∂((multHaar F).prod (selfDualMeasure ψ)) = gam3 ψ ν c s * ∫ a, zF W c s a ∂multHaar F

end D

end Ad3.LFS
