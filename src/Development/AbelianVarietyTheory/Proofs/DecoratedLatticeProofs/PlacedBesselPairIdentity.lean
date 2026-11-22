import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterAdelicUnitaryGroupFinitePartScalar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseMovesVectorZ
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelIntegralTwist

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.MiTop

theorem lattice_ratio_vector_of_scalar_factorisation {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (e c θ θ' : R)
    (X X' Sm Sm' Kk Z : GL n R) (hZ : Z.val = c • (1 : Matrix n n R))
    (hT : X⁻¹ * Sm = Z * (X'⁻¹ * Sm') * Kk) (zY zY' Γ : n → R)
    (hm : e • Matrix.mulVec (Sm⁻¹).val zY = e • (θ • Γ)) (hm' : e • Matrix.mulVec (Sm'⁻¹).val zY' = e • (θ' • Γ)) :
    e • ((θ * c) • Matrix.mulVec ((X'⁻¹ * Sm') * Kk * (X'⁻¹ * Sm')⁻¹).val (Matrix.mulVec (X'⁻¹).val zY')) =
      e • (θ' • Matrix.mulVec (X⁻¹).val zY) := by
  set M := (X'⁻¹ * Sm') * Kk * (X'⁻¹ * Sm')⁻¹ with hM
  have hg : Z * M * X'⁻¹ = (X⁻¹ * Sm) * Sm'⁻¹ := by
    rw [hM, hT]; group
  have h2 : c • Matrix.mulVec M.val (Matrix.mulVec (X'⁻¹).val zY') = Matrix.mulVec (Z * M * X'⁻¹).val zY' := by
    have : (Z * M * X'⁻¹).val = c • (M.val * (X'⁻¹).val) := by
      rw [Units.val_mul, Units.val_mul, hZ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [this, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have h3 : e • (θ • Matrix.mulVec (Sm'⁻¹).val zY') = e • (θ' • Matrix.mulVec (Sm⁻¹).val zY) := by
    rw [smul_comm e θ (Matrix.mulVec (Sm'⁻¹).val zY'), hm', smul_comm e θ' (Matrix.mulVec (Sm⁻¹).val zY), hm,
      smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  rw [mul_smul, h2, hg, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, h3,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul]
  congr 3
  group

theorem redFn_scalar_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Formalism.L2.DIV.Pl E)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (c : E ⊗[F] Formalism.L2.Herm.Af F) (hx : x ∈ Formalism.L2.DIV.St β)
    (hc : x.val = c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (i₀ : Fin n) :
    ∃ hci : c ∈ Formalism.L2.Herm.intAf F E,
      (Formalism.L2.DIV.resS F PP ⟨c, hci⟩ = 1 → Formalism.L2.DIV.redFn β PP x = 1) := by
  obtain ⟨y, rfl⟩ := hx
  have hy : (Formalism.L2.DIV.intGL F E n y).val = c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    have e1 : Formalism.L2.DIV.intGL F E n y = β⁻¹ * Formalism.L2.DIV.frGL β y * β := by
      simp only [Formalism.L2.DIV.frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e1, Units.val_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  have hent : ∀ i j, ((y.val i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
      (c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) i j := fun i j => by
    rw [← hy]; rfl
  have hci : c ∈ Formalism.L2.Herm.intAf F E := by
    have h := hent i₀ i₀
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    rw [← h]; exact (y.val i₀ i₀).2
  refine ⟨hci, fun h1 => ?_⟩
  rw [Formalism.L2.DIV.redFn_frGL]
  apply Units.ext
  ext i j
  have hyij : y.val i j = if i = j then ⟨c, hci⟩ else 0 := by
    apply Subtype.ext
    rw [hent i j, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  show Formalism.L2.DIV.resS F PP (y.val i j) = (1 : Matrix (Fin n) (Fin n) _) i j
  rw [hyij, Matrix.one_apply]
  split_ifs <;> simp [h1]

end GlobalTheory.MiTop

end
