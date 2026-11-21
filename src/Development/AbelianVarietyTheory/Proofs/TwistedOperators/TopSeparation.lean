import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactMeetsBesselTopRationalOrbits
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneAdditiveBoundedCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneSimultaneousRightTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneRightTranslateUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbRelAtRealPlaceOfUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtRealPlaceMemUnipotentFlagAdelic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

noncomputable section

namespace GlobalTheory.SepRows.SepProof

section
open Classical

theorem atTau_mem_GinfC' {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    atTau θ V τ g ∈ GinfC V := by
  unfold atTau; split_ifs with h
  exacts [h.choose_spec.1, one_mem _]

theorem pairVec_comp_rho {D : D7} {V : HSp D} (c : CoefA V) (ξ : Module.Dual ℂ c.W) (Ψ : Bridge.Gf V → c.W) {a : GA D V}
    (ha : a ∈ GinfC V) : pairVec c (ξ ∘ₗ c.ρ a⁻¹) Ψ = rTr V a (pairVec c ξ Ψ) := by
  funext h
  have e : (finHom V).rangeRestrict (h * a) = (finHom V).rangeRestrict h := by
    rw [map_mul]
    have : (finHom V).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    rw [this, mul_one]
  simp only [rTr, pairVec_apply, e, mul_inv_rev, map_mul, LinearMap.comp_apply, Module.End.mul_apply]

theorem mult_equiv {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) {T : MMap M} (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ) (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => rfl
  | add T₁ T₂ _ _ h₁ h₂ =>
    simp only [MultilinearMap.add_apply, h₁, h₂]; rfl
  | smul c T _ h =>
    simp only [MultilinearMap.smul_apply, h]; rfl

end

theorem Bplus_smul_left {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (a : ℂ)
    (φ : GA D (G.V (.top 0)) → ℂ) (F : GA D (G.V (.grid D.R.m 0)) → ℂ) : Bplus W M (a • φ) F = a * Bplus W M φ F := by
  have e : ∀ h n, besInt W (a • φ) F h n = a * besInt W φ F h n := fun h n => by
    simp only [besInt, Pi.smul_apply, smul_eq_mul]; ring
  simp only [Bplus, e, integral_const_mul]

theorem Bplus_smul_right {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (a : ℂ)
    (φ : GA D (G.V (.top 0)) → ℂ) (F : GA D (G.V (.grid D.R.m 0)) → ℂ) : Bplus W M φ (a • F) = a * Bplus W M φ F := by
  have e : ∀ h n, besInt W φ (a • F) h n = a * besInt W φ F h n := fun h n => by
    simp only [besInt, Pi.smul_apply, smul_eq_mul]; ring
  simp only [Bplus, e, integral_const_mul]

end GlobalTheory.SepRows.SepProof

end
