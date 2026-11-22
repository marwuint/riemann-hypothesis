import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFiniteAdeleOfSplitPlaceComponents
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLocalFactorEqIteratedChainDatum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.MovedDat

open GlobalTheory.LocMod.StepVec

theorem mt_mul {D : D7} (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one {D : D7} (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem mt_inv_mul {D : D7} (V : HSp D) (a : GA D V) : mt V a⁻¹ * mt V a = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

theorem isHalf_mul {D : D7} {S T : HSp D} (e : AE D) (A : Matrix (Fin T.rank) (Fin T.rank) (AE D))
    (B : Matrix (Fin S.rank) (Fin S.rank) (AE D)) (y : WO S T) (hy : IsHalf e y) :
    IsHalf e (HMul.hMul (HMul.hMul A (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) B : WO S T) := by
  intro i j
  have hy' : e • (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) :=
    Matrix.ext fun i j => hy i j
  have := congrFun (congrFun (congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) => HMul.hMul (HMul.hMul A M) B) hy') i) j
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at this
  exact this

theorem isHalf_actO_iff {D : D7} (S T : HSp D) (g : GA D S) (h : GA D T) (e : AE D) (x : WO S T) :
    IsHalf e (actO S T g h x) ↔ IsHalf e x := by
  constructor
  · intro hx
    have e1 : x = actO S T g⁻¹ h⁻¹ (actO S T g h x) := by
      unfold actO
      rw [inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul, Matrix.mul_assoc,
        mt_inv_mul, Matrix.mul_one]
    rw [e1]
    exact isHalf_mul e _ _ _ hx
  · intro hx
    exact isHalf_mul e _ _ _ hx

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem down_moved_actO (p : Place D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (g : GA D S) (h : GA D T) (x : WO S T) :
    p.down (moved p FS g⁻¹) (moved p FT h⁻¹) (actO S T g⁻¹ h⁻¹ x) = p.down FS FT x := by
  have hm : ∀ (V : HSp D) (a : GA D V), (mt V a⁻¹⁻¹).map p.π * (mt V a⁻¹).map p.π = 1 := fun V a => by
    rw [← Matrix.map_mul, mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold Place.down moved actO
  simp only [Matrix.map_mul]
  have e1 : FT.γ * (mt T h⁻¹⁻¹).map p.π * ((mt T h⁻¹).map p.π * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π *
      (mt S g⁻¹⁻¹).map p.π) * ((mt S g⁻¹).map p.π * FS.β) =
      FT.γ * ((mt T h⁻¹⁻¹).map p.π * (mt T h⁻¹).map p.π) * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π *
        ((mt S g⁻¹⁻¹).map p.π * (mt S g⁻¹).map p.π) * FS.β := by
    simp only [Matrix.mul_assoc]
  rw [e1, hm, hm, Matrix.mul_one, Matrix.mul_one]

end GlobalTheory.MovedDat

namespace GlobalTheory.MovedDat

end GlobalTheory.MovedDat

namespace GlobalTheory.MovedDat

end GlobalTheory.MovedDat

end
