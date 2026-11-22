import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

noncomputable section

namespace GlobalTheory.LieDisc.ImIndex

open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def dm (E : Type) [Field E] [NumberField E] [IsCMField E] : E →ₗ[ℚ] E where
  toFun x := x - cc x
  map_add' x y := by simp only [cc, map_add]; ring
  map_smul' q x := by simp only [cc, map_rat_smul, RingHom.id_apply, smul_sub]

theorem mem_ker_dm {x : E} : x ∈ LinearMap.ker (dm E) ↔ x ∈ maximalRealSubfield E := by
  rw [LinearMap.mem_ker, ← IsCMField.complexConj_eq_self_iff]
  change x - cc x = 0 ↔ _
  rw [sub_eq_zero, eq_comm]; rfl

def kerEquiv (E : Type) [Field E] [NumberField E] [IsCMField E] :
    LinearMap.ker (dm E) ≃ₗ[ℚ] maximalRealSubfield E where
  toFun x := ⟨x.1, mem_ker_dm.1 x.2⟩
  invFun y := ⟨y.1, mem_ker_dm.2 y.2⟩
  map_add' x y := rfl
  map_smul' q x := by ext; simp [Rat.smul_def]
  left_inv x := rfl
  right_inv y := rfl

instance : Module.Finite ℤ (imLat E) := by
  let f : imLat E →+ 𝓞 E :=
    { toFun := fun x => ⟨x.1, x.2.1⟩
      map_zero' := rfl
      map_add' := fun x y => rfl }
  exact Module.Finite.of_injective f.toIntLinearMap (fun x y h => Subtype.ext (congrArg Subtype.val h :))

instance : Module.Free ℤ (imLat E) := Module.free_of_finite_type_torsion_free'

end GlobalTheory.LieDisc.ImIndex
