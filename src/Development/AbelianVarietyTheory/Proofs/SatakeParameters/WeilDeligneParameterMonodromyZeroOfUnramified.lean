import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.TameType

theorem irreducible_twist {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ Γ V}
    (h : ρ.IsIrreducible) (ν : Γ →* ℂˣ) : (twist ρ ν).IsIrreducible := by
  let f : Subrepresentation (twist ρ ν) → Subrepresentation ρ := fun S =>
    ⟨S.toSubmodule, fun g v hv => by
      have h1 := S.toSubmodule.smul_mem ((ν g)⁻¹ : ℂˣ).1 (S.apply_mem_toSubmodule g hv)
      simpa [smul_smul] using h1⟩
  have hn : (⊥ : Submodule ℂ V) ≠ ⊤ := fun e =>
    (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective e)
  have : Nontrivial (Subrepresentation (twist ρ ν)) := ⟨⊥, ⊤, fun e =>
    hn (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  rcases eq_bot_or_eq_top (f S) with e | e
  · exact Or.inl (Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule e :))
  · exact Or.inr (Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule e :))

theorem charpoly_scalar {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (z : ℂ) :
    (z • (1 : Module.End ℂ V)).charpoly = (X - C z) ^ Module.finrank ℂ V := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, LinearMap.toMatrix_one,
    Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp

section WD

open GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem weilDeligneParameter_monodromy_zero_of_unramified {a : WD h} (ha : a.unr) : a.mono0 := by
  induction a using WD.ind
  exact (WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 ((WD.unr_mk _).1 ha).1

theorem inePol_of_unr {a : WD h} (ha : a.unr) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B) :
    a.inePol σ = (X - 1) ^ a.lpDim := by
  induction a using WD.ind
  rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, ((WD.unr_mk _).1 ha).2, WD.lpDim_mk, LinearMap.charpoly_one]

theorem inePol_char_of_unr {a c : WD h} (ha : a.unr) (hc : c.lpDim = 1) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B)
    {z : ℂ} (hz : c.inePol σ = X - C z) : (a.lpChar c).inePol σ = (X - C z) ^ a.lpDim := by
  rw [← WD.lpDim_char a c hc]
  induction a using WD.ind with
  | hP m a =>
  induction c using WD.ind with
  | hP n c =>
    rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk] at hz
    have h1 := LinearMap.aeval_self_charpoly (c.ρ (ineIncl h ⟨σ, hσ⟩))
    rw [hz, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h1
    rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.lpDim_mk, WDRep.tensor_ρ,
      ((WD.unr_mk _).1 ha).2, h1, TensorProduct.map_smul_right, TensorProduct.map_one, charpoly_scalar]

end WD

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.TameType
