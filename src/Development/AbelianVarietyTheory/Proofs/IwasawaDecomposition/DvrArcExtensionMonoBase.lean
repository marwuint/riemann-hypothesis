import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelReps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Formalism.LocalToGlobal.ProjectiveLattices.ArcPtX
import Formalism.LocalToGlobal.ProjectiveLattices.ArcTheta
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcExt

theorem exists_ramified_ext (T : CDVR) {Ω : Type} [Field Ω] [Algebra T.Fr Ω] [Algebra.IsAlgebraic T.Fr Ω] [IsAlgClosed Ω]
    (M : IntermediateField T.Fr Ω) [FiniteDimensional T.Fr M] (N : ℕ) (hN : 0 < N) (ϖ₀ : T.V) (h₀ : Irreducible ϖ₀) :
    ∃ (T' : CDVR) (g : T.V →+* T'.V) (κ : M →+* T'.Fr) (e : ℕ) (ϖ : T'.V),
      Function.Injective g ∧ IsLocalHom g ∧ Irreducible ϖ ∧
      (∀ v, κ (algebraMap T.Fr M (algebraMap T.V T.Fr v)) = algebraMap T'.V T'.Fr (g v)) ∧
      N ∣ e ∧ Associated (g ϖ₀) (ϖ ^ e) := by
  haveI : CharZero T.Fr := algebraRat.charZero _
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap T.Fr Ω (algebraMap T.V T.Fr ϖ₀)) hN
  let A := IntermediateField.adjoin T.Fr ({α} : Set Ω)
  have : FiniteDimensional T.Fr A := IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  let L : IntermediateField T.Fr Ω := M ⊔ A
  have : FiniteDimensional T.Fr L := inferInstance
  obtain ⟨W, _, _, _, _, _, _, _, hc, -, hinj, hloc, -, -⟩ := GlobalTheory.SS.exists_complete_dvr_finite_extension T.V T.Fr L
  have : CharZero W := charZero_of_injective_algebraMap hinj
  let T' : CDVR := { V := W }
  let ψ : L ≃+* FractionRing W := (FractionRing.algEquiv W L).symm.toRingEquiv
  have hψ : ∀ w : W, ψ (algebraMap W L w) = algebraMap W (FractionRing W) w := fun w =>
    (FractionRing.algEquiv W L).symm.commutes w
  let κ : M →+* FractionRing W := ψ.toRingHom.comp (IntermediateField.inclusion (le_sup_left : M ≤ L)).toRingHom
  have hκ : ∀ v, κ (algebraMap T.Fr M (algebraMap T.V T.Fr v)) = algebraMap W (FractionRing W) (algebraMap T.V W v) := by
    intro v
    have h1 : algebraMap T.Fr L (algebraMap T.V T.Fr v) = algebraMap W L (algebraMap T.V W v) :=
      (RingHom.congr_fun hc v).symm
    rw [← hψ, ← h1]
    rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hg0 : algebraMap T.V W ϖ₀ ≠ 0 := fun h => h₀.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hϖ
  have hαL : α ∈ L := (le_sup_right : A ≤ L) (IntermediateField.mem_adjoin_simple_self T.Fr α)
  let b : FractionRing W := ψ ⟨α, hαL⟩
  have hb : b ^ N = algebraMap W (FractionRing W) (algebraMap T.V W ϖ₀) := by
    have h1 : (⟨α, hαL⟩ : L) ^ N = algebraMap W L (algebraMap T.V W ϖ₀) := by
      apply Subtype.ext
      have h2 := RingHom.congr_fun hc ϖ₀
      refine hα.trans ?_
      exact (congrArg (L.val) h2.symm)
    rw [← hψ, ← h1, map_pow]
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow hN.ne'] at hb
    exact hg0 ((IsFractionRing.injective W (FractionRing W)) (by rw [← hb, map_zero]))
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := W) b
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [← hxy, map_zero, zero_div])
  obtain ⟨m, v₁, hv₁⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨n, v₂, hv₂⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hW : x ^ N = algebraMap T.V W ϖ₀ * y ^ N := by
    apply IsFractionRing.injective W (FractionRing W)
    have hy' : algebraMap W (FractionRing W) y ≠ 0 := by
      simpa using hy0
    rw [map_pow, map_mul, map_pow, ← hb, ← hxy, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hy')]
  have he : m * N = e + n * N := by
    rw [hv₁, hv₂, hu, mul_pow, mul_pow, ← pow_mul, ← pow_mul] at hW
    have : ((v₁ ^ N : Wˣ) : W) * ϖ ^ (m * N) = ((u * v₂ ^ N : Wˣ) : W) * ϖ ^ (e + n * N) := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hW, pow_add]
      ring
    exact IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ _ _ _ _ this
  refine ⟨T', algebraMap T.V W, κ, e, ϖ, hinj, hloc, hϖ, hκ, ?_, ?_⟩
  · have : N ∣ e + n * N := ⟨m, by rw [← he, mul_comm]⟩
    exact (Nat.dvd_add_left (Dvd.intro_left n rfl)).1 this
  · exact ⟨u⁻¹, by
      show algebraMap T.V W ϖ₀ * ((u⁻¹ : Wˣ) : W) = ϖ ^ e
      rw [hu, mul_comm (u : W), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩

end GlobalTheory.ArcExt
