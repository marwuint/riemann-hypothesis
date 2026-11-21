import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsSumOfSelf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL

section Local

variable {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
  {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

def AbW (x : WD h) : Prop :=
  ∀ g g' : Weil h, x.charPol (g * g' * g⁻¹ * g'⁻¹) = (Polynomial.X - 1) ^ x.lpDim

structure Near (x y : WD h) : Prop where
  mono : x.mono0 ↔ y.mono0
  size : ∀ σ : Weil h, (x.eig σ).map (fun z => ‖z‖) = (y.eig σ).map (fun z => ‖z‖)
  eq : ∀ (χ : Weil h →* ℂˣ) (hχ : GlobalTheory.WeilDeligne.IsSmooth χ), IneTriv (y.lpTwist χ hχ) → x = y
  tame : ∀ (χ : Weil h →* ℂˣ) (hχ : GlobalTheory.WeilDeligne.IsSmooth χ), IsTameWD (y.lpTwist χ hχ) →
    ∀ τ : Ine (F := K) A, x.charPol (ineIncl h τ) = y.charPol (ineIncl h τ)

theorem Near.refl (x : WD h) : Near x x := ⟨Iff.rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem Near.of_eq {x y : WD h} (e : x = y) : Near x y := e ▸ Near.refl x

end Local

def SolvDisj {K Ω : Type} (M : Type) [Field K] [Field M] [Field Ω] [Algebra K Ω] [Algebra M Ω] [Algebra K M] [IsScalarTower K M Ω]
    (N : Subgroup (G K Ω)) : Prop :=
  IsGalois K M ∧ IsSolvable (M ≃ₐ[K] M) ∧
    ∀ g : G K Ω, ∃ (x : G M Ω) (n : G K Ω), n ∈ N ∧ g = AlgEquiv.restrictScalarsHom K x * n

end GlobalTheory.AboveL

end
