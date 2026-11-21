import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq

noncomputable section

namespace GlobalTheory.SplitRead.BlockParam

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
open GlobalTheory.WeilDeligne (WD Weil ineIncl)

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem charpoly_smul_one {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (c : ℂ) :
    (c • (1 : Module.End ℂ V)).charpoly = (X - C c) ^ Module.finrank ℂ V := by
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, LinearMap.toMatrix_one,
    Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp

theorem charPol_lpChar_of_unr (a χ : WD h) (ha : a.unr) (σ : Ine (F := E) B) (c : ℂ)
    (hc : χ.charPol (ineIncl h σ) = X - C c) :
    (a.lpChar χ).charPol (ineIncl h σ) = (X - C c) ^ a.lpDim := by
  have hd : χ.lpDim = 1 := by rw [← WD.charPol_natDegree χ (ineIncl h σ), hc, natDegree_X_sub_C]
  induction a using WD.ind with
  | hP n a =>
  induction χ using WD.ind with
  | hP m b =>
    rw [WD.unr_mk] at ha
    rw [WD.lpDim_mk] at hd
    rw [WD.charPol_mk] at hc
    have h3 := LinearMap.aeval_self_charpoly (b.ρ (ineIncl h σ))
    rw [hc, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h3
    rw [WD.lpChar_mk, WD.charPol_mk, WD.lpDim_mk, GlobalTheory.WeilDeligne.WDRep.tensor_ρ, ha.2, h3,
      TensorProduct.map_smul_right, TensorProduct.map_one, charpoly_smul_one, Module.finrank_tensorProduct, hd,
      mul_one]

theorem irreducible_twist {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ Γ V}
    (hρ : ρ.IsIrreducible) (χ : Γ →* ℂˣ) : (twist ρ χ).IsIrreducible :=
  OrderIso.isSimpleOrder_iff (α := Subrepresentation (twist ρ χ)) (β := Subrepresentation ρ)
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        simpa [smul_smul] using this⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl } |>.2 hρ

def detIrr (n : ℕ) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Irr k n where
  V := ℂ
  π := detRep (Fin n) χ
  smooth := (isSmooth_ofChar_iff _).2 hχ.detChar
  irr := isIrreducible_ofChar _

def twistIrr {n : ℕ} (π : Irr k n) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Irr k n where
  V := π.V
  π := twist π.π (detChar (Fin n) χ)
  smooth := isSmooth_twist π.smooth hχ.detChar
  irr := irreducible_twist π.irr _

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.SplitRead.BlockParam
