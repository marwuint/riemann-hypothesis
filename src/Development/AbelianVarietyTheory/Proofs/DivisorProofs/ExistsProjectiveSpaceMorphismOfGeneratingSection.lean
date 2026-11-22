import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientsTranscendenceBasisBasepointFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotientSubfieldEqMulRankOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceOrderArithVarietyFubiniStudyDegre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithCharZeroFunctionFieldInjectiveConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismProjSpaceBasepointFreeSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapGenericPointEqOfAlgIndependentQuotients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointEqFinrankQuotients

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem toProj_gens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ (_ : IsIntegral (PSpace k D)) (π : X ⟶ PSpace k D) (hπ : π ≫ PSpace.str k D = p), π (genericPoint X) = genericPoint (PSpace k D) ∧ π.residueDegree (genericPoint X) ≠ 0 ∧ π.residueDegree (genericPoint X) * Module.finrank ℤ k = Module.finrank (ratF x) X.functionField ∧ ∀ u : SmFn p, IsCan P e 1 x u → ((up P.L u).pow e).Isometric ((ProjSpace.hermitianTwistingSheaf k D).pull π hπ) := by
  intro k _ X _ p D hX P hA e x hg
  obtain ⟨hx, hind, hfin⟩ := _root_.GlobalTheory.HSAmp.gens_quot_trBasis k X p D hX P hA e x hg
  obtain ⟨hK, hι⟩ := _root_.GlobalTheory.isArithVar_charZero_functionField_and_injective k X p D hX
  haveI := hX.isDomain
  haveI := hX.finite
  haveI : CharZero k := ⟨fun a b h => Nat.cast_injective (R := X.functionField) (by
    have := congrArg (GlobalTheory.toFunctionField p) h
    simpa only [map_natCast] using this)⟩
  obtain ⟨hP, -, -⟩ := _root_.GlobalTheory.PSpaceDeg.main k D
  haveI : IsIntegral (PSpace k D) := hP.isIntegral
  obtain ⟨hdeg, hev⟩ := GlobalTheory.T.finrank_quotientSubfield_eq_mul_rank_order k X.functionField (GlobalTheory.toFunctionField p) D x hι hind
  obtain ⟨π, hπ, hc, hiso⟩ := _root_.GlobalTheory.HSAmp.GenMap.toProj_gens k X p D hX P e x hg (hx 0)
  have hgen := _root_.GlobalTheory.GenericImage.map_genericPoint_eq k X p D π hπ x (hx 0) hc hev
  have hr := _root_.GlobalTheory.GenericResidueDegree.residueDegree_eq_finrank_quotients k X p D π hπ x (hx 0) hc hgen
  refine ⟨inferInstance, π, hπ, hgen, ?_, ?_, hiso⟩
  · rw [hr]
    intro h0
    haveI := hfin
    have : 0 < Module.finrank (ratF x) X.functionField := Module.finrank_pos
    rw [hdeg, h0, zero_mul] at this
    exact lt_irrefl _ this
  · rw [hr, hdeg]

end GlobalTheory.HSAmp
