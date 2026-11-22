import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMatMapSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedDiagonalIntegralLinearForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalUnitaryActionPreserves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicLeviInverseQuotientDetNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapNegApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentCharacterValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelLocalTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.DblLocal

open MeasureTheory GlobalTheory.HoweLocal GlobalTheory.LatVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Lift

theorem liftE_eq (v : Pl F) (y : Fv F v ⊗[F] E) : liftE v y = Supp.singleTens E v y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_liftE_mul (v : Pl F) {a b c : Type} [Fintype b] (x : Matrix a b (Fv F v ⊗[F] E)) (P : Matrix b c (AE F E)) :
    x.map (liftE v) * P = (x * P.map (compFin F E v)).map (liftE v) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, liftE_eq, Supp.singleTens_mul]

theorem mul_map_liftE (v : Pl F) {a b c : Type} [Fintype b] (P : Matrix a b (AE F E)) (x : Matrix b c (Fv F v ⊗[F] E)) :
    P * x.map (liftE v) = (P.map (compFin F E v) * x).map (liftE v) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, liftE_eq]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_comm, Supp.singleTens_mul, mul_comm]

theorem map_liftE_map (v : Pl F) {a b : Type} (x : Matrix a b (Fv F v ⊗[F] E)) :
    (x.map (liftE v)).map (compFin F E v) = x := by
  ext i j
  simp only [Matrix.map_apply, liftE_eq, Supp.compFin_singleTens_self]

theorem map_liftE_cA (σ : E →ₐ[F] E) (v : Pl F) {a b : Type} (x : Matrix a b (Fv F v ⊗[F] E)) :
    (x.map (liftE v)).map (cA σ) = (x.map (cv σ v)).map (liftE v) := by
  ext i j
  simp only [Matrix.map_apply]
  induction x i j using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {β : Type} [Fintype β] [DecidableEq β]

def liftM (v : Pl F) (β : Type) [Fintype β] [DecidableEq β] : Matrix β β (Fv F v ⊗[F] E) →* Matrix β β (AE F E) where
  toFun h := 1 + (h - 1).map (liftE v)
  map_one' := by simp
  map_mul' a b := by
    have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
    have e2 : ((a - 1) * (b - 1)).map (liftE v) = (a - 1).map (liftE v) * (b - 1).map (liftE v) := by
      rw [map_liftE_mul, map_liftE_map]
    rw [e, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), e2]
    noncomm_ring

theorem liftM_apply (v : Pl F) (h : Matrix β β (Fv F v ⊗[F] E)) : liftM v β h = 1 + (h - 1).map (liftE v) := rfl

theorem liftM_mem (σ : E →ₐ[F] E) (v : Pl F) {J : Matrix β β (AE F E)} {JL : Matrix β β (Fv F v ⊗[F] E)}
    (hJ : J.map (compFin F E v) = JL) (h : UG (cv σ v) JL) : Units.map (liftM v β) h.1 ∈ UG (cA σ) J := by
  have hh : (h.1 : Matrix β β (Fv F v ⊗[F] E))ᵀ * JL * (h.1 : Matrix β β (Fv F v ⊗[F] E)).map (cv σ v) = JL := h.2
  show (liftM v β h.1.1)ᵀ * J * (liftM v β h.1.1).map (cA σ) = J
  obtain ⟨a, ha⟩ : ∃ a, (h.1 : Matrix β β (Fv F v ⊗[F] E)) = 1 + a := ⟨h.1.1 - 1, by abel⟩
  rw [ha] at hh
  rw [ha, liftM_apply, add_sub_cancel_left]
  rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_add,
    Matrix.transpose_one] at hh ⊢
  rw [map_liftE_cA, ← Matrix.transpose_map]
  set c := a.map (cv σ v)
  have h0 : aᵀ * JL + JL * c + aᵀ * JL * c = 0 := by
    rw [← sub_eq_zero] at hh
    rw [← hh]; noncomm_ring
  have e1 : aᵀ.map (liftE v) * J = (aᵀ * JL).map (liftE v) := by rw [map_liftE_mul, hJ]
  have e2 : J * c.map (liftE v) = (JL * c).map (liftE v) := by rw [mul_map_liftE, hJ]
  have e3 : aᵀ.map (liftE v) * J * c.map (liftE v) = (aᵀ * JL * c).map (liftE v) := by
    rw [e1, map_liftE_mul, map_liftE_map]
  have h1 : aᵀ.map (liftE v) * J + J * c.map (liftE v) + aᵀ.map (liftE v) * J * c.map (liftE v) = 0 := by
    rw [e3, e1, e2, ← Matrix.map_add _ (map_add _), ← Matrix.map_add _ (map_add _), h0, Matrix.map_zero _ (map_zero _)]
  rw [← sub_eq_zero, ← h1]
  noncomm_ring

def liftU (σ : E →ₐ[F] E) (v : Pl F) {J : Matrix β β (AE F E)} {JL : Matrix β β (Fv F v ⊗[F] E)}
    (hJ : J.map (compFin F E v) = JL) : UG (cv σ v) JL →* UG (cA σ) J :=
  ((Units.map (liftM v β)).comp (UG (cv σ v) JL).subtype).codRestrict _ (liftM_mem σ v hJ)

theorem liftU_val (σ : E →ₐ[F] E) (v : Pl F) {J : Matrix β β (AE F E)} {JL : Matrix β β (Fv F v ⊗[F] E)}
    (hJ : J.map (compFin F E v) = JL) (h : UG (cv σ v) JL) :
    ((liftU σ v hJ h : GL β (AE F E)) : Matrix β β (AE F E)) = liftM v β (h : GL β (Fv F v ⊗[F] E)) := rfl

end Lift

end GlobalTheory.HoweLocal.DblLocal
