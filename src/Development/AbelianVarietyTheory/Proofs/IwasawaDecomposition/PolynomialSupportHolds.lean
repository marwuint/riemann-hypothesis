import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.PsJetEqToJetOfNonempty
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoOfAmpleDeterminantFrames
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsProperSemiAbelianTripleOfAbelianLocusEqUniv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section Form

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_periodForm {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W]
    [IsAdicComplete (maximalIdeal W) W] {t : SAB H (Sp W)}
    (P : PELUnif (maximalIdeal W) t) {ϖ : W} (hϖ : Irreducible ϖ) :
    ∃ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] ∧ ∀ y, y ≠ 0 → 0 < be y y := by
  letI := H.starRing
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have hQ' : QForm.IsQ P.D.toPre ϖ Q := hQ
  have hex : ∀ χ, ∃ r, PsiCoord P.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main W P.D inferInstance χ).1).imp fun _ h => h.1
  have h0 : ∀ a, 0 ≤ Q a := fun a => by
    by_cases ha : a = 0
    · rw [ha, QForm.Q_zero hϖ P.D hQ']
    · exact zero_le_one.trans (QForm.Q_pos hϖ P.D hQ' ha)
  let be : LinearMap.BilinForm ℤ P.D.toPre.X :=
    LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D hQ' a b)
      (fun a a' b => by simp only [map_add, AddMonoidHom.add_apply])
      (fun c a b => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_id])
      (fun a b b' => by simp only [map_add])
      (fun c a b => by simp only [map_zsmul, smul_eq_mul, zsmul_eq_mul, Int.cast_id])
  have hbe : ∀ a b, be a b = QForm.bOf P.D.toPre Q a b := fun _ _ => rfl
  refine ⟨be, ⟨fun a b => ?_, fun x a b => ?_, fun a b => ?_⟩, fun y => ?_, fun y hy => ?_⟩
  · rw [hbe, hbe, QForm.bOf_comm]
  · rw [hbe, hbe]
    exact QForm.bOf_balance hϖ P.D GlobalTheory.allSixLaws.1 P.oD hQ' x a b
  · simp
  · obtain ⟨r, hr⟩ := hex y
    obtain ⟨u, hu⟩ := GlobalTheory.ValForm.hasVal_coord (hQ y) hr
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h0 y)
    rw [hn, zpow_natCast, ← map_pow, ← map_mul] at hu
    have e : r = u * ϖ ^ n := (IsFractionRing.injective W (FractionRing W) hu).trans (_root_.mul_comm _ _)
    refine ⟨u, fun _ => n, fun i => ?_, ?_⟩
    · have : i = 0 := Subsingleton.elim _ _
      subst this
      show be y y = _
      rw [hbe, ← QForm.two_Q_eq hϖ P.D hQ', hn]
    · simpa [e] using hr
  · rw [hbe, ← QForm.two_Q_eq hϖ P.D hQ']
    have := QForm.Q_pos hϖ P.D hQ' hy
    omega

end Form

section Trait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem closed_mem_abLocus_iff (T : CDVR) {t : SAB H (Sp T.V)} (P : PELUnif (maximalIdeal T.V) t) :
    (closedPoint T.V : Sp T.V) ∈ abLocus t.G ↔ Subsingleton P.D.toPre.X := by
  constructor
  · intro hc
    have hmax : (maximalIdeal T.V ^ (0 + 1)).IsMaximal := by
      rw [zero_add, pow_one]; infer_instance
    have hF : IsField (T.V ⧸ maximalIdeal T.V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
    have hle : maximalIdeal T.V ^ (0 + 1) ≤ (closedPoint T.V).asIdeal := by
      rw [zero_add, pow_one]; exact le_rfl
    obtain ⟨q, hq⟩ : closedPoint T.V ∈ Set.range (PrimeSpectrum.comap
        (Ideal.Quotient.mk (maximalIdeal T.V ^ (0 + 1)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      exact hle
    let g := P.U.gt 0
    have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
    have hq' : thick T.V (maximalIdeal T.V) 0 q ∈ abLocus t.G := by
      rw [← hq] at hc; exact hc
    exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF _ q hq' P.D.toPre.X g.i g.i_hom
  · intro hs K _ _ s _
    have := (isAbelianScheme_of_unif_of_subsingleton GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 T.V T.cpl P.D P.A t.G t.semi
      P.U hs).proper
    infer_instance

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end Trait

end GlobalTheory.TorRef
