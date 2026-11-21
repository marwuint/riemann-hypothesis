import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel.BoundProof

section Gen

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem actV_mem_latT (a : Λ) {y : P.V} (hy : y ∈ P.latT) : P.actV a y ∈ P.latT :=
  (P.mem_latT_iff _).2 fun t => by
    obtain ⟨c, hc⟩ := (P.mem_latT_iff y).1 hy (P.actT (star a) t)
    exact ⟨c, by rw [hc, P.pairV_act]; rfl⟩

theorem pairV_inclT_mem {u : P.V} (hu : u ∈ P.latT) (y : O ⊗[ℤ_[p]] P.T) :
    P.pairV u (P.inclT y) ∈ (algebraMap O C).range := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add, map_add, map_add, ha, hb]⟩
  | tmul c t =>
    obtain ⟨b, hb⟩ := (P.mem_latT_iff u).1 hu t
    refine ⟨c * b, ?_⟩
    have e : (algebraMap O C c ⊗ₜ[ℤ_[p]] t : P.V) = algebraMap O C c • ((1 : C) ⊗ₜ[ℤ_[p]] t) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [P.inclT_tmul, e, map_smul, smul_eq_mul, map_mul, hb]

end Gen

section Gen2

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem pairV_bLie_inclT (x : LieG P.Gt) (y : O ⊗[ℤ_[p]] P.T) :
    P.pairV (P.bLie x) (P.inclT y) = algebraMap O C ((P.al y).1 x) := by
  rw [pairV_bLie_eq_evLie, P.alC_inclT, Point.inclOm, TensorProduct.mk_apply, evLie,
    LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end Gen2

end GlobalTheory.FlatModel.BoundProof

namespace GlobalTheory.FlatModel

end GlobalTheory.FlatModel
