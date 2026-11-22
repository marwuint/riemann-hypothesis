import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyTwistedSectionComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.GenShift

open IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c}

theorem exists_twPow (s : TwSec U x Z (wtOf Dw 0 1)) : ∀ n : ℕ, Nonempty (TwSec U x Z (wtOf Dw 0 (n : ℤ)))
  | 0 => ⟨(TwSec.const x s.pts 1 one_ne_zero).copy (by rw [Nat.cast_zero, wtOf_zero])⟩
  | n + 1 => by
    obtain ⟨t⟩ := exists_twPow s n
    exact ⟨(t.mul s).copy (by rw [← wtOf_add, add_zero]; push_cast; rfl)⟩

set_option maxHeartbeats 1000000 in

theorem span_latW_add (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G G₀ : WTZ E) (hG : Even G.2)
    (hs : ∀ Z : Comp Xo c, Nonempty (TwSec U x Z G₀))
    (h : Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) = ⊤) :
    Submodule.span c.F (latW U (G + G₀) : Set (cuspW Xo c U (G + G₀))) = ⊤ := by
  classical
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [eq_top_iff]
  intro F _
  have hF : F = ∑ Z : Comp Xo c,
      (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U (G + G₀)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact (sum_idem_mul _).symm
  rw [hF]
  refine Submodule.sum_mem _ fun Z _ => ?_
  obtain ⟨s⟩ := hs Z
  obtain ⟨φ, -, -, hA, -⟩ := GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨a, ha0, hlo, -⟩ := GlobalTheory.FlatTw.Good.exists_twist_scalar s
  let p : cuspOn U Z (G + G₀) := ⟨idem Z * (F : Rul Xo c),
    GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2, by rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)⟩
  let g : cuspOn U Z G := φ.symm p
  have hmem : (⟨(g : Rul Xo c), g.2.1⟩ : cuspW Xo c U G) ∈ Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) := by
    rw [h]; trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 c.F)) c.F _ _ hmem
  rw [Submodule.span_eq, Submonoid.smul_def, ← algebraMap_smul c.F] at ht
  set d : c.F := algebraMap (𝓞 c.F) c.F t with hd
  have hd0 : d ≠ 0 := by simpa [hd] using nonZeroDivisors.ne_zero t.2
  have hf : d • g ∈ latOn U Z G := (mem_latOn U).2 ht
  have hq := hA a ha0 hlo (d • g) hf ((a * d) • p) (by
    simp only [g, map_smul, LinearEquiv.apply_symm_apply, Submodule.coe_smul, smul_smul])
  have hq' := (mem_latOn U).1 hq
  have had : a * d ≠ 0 := mul_ne_zero ha0 hd0
  have e : (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U (G + G₀)) =
      (a * d)⁻¹ • (⟨(((a * d) • p : cuspOn U Z (G + G₀)) : Rul Xo c), ((a * d) • p).2.1⟩ : cuspW Xo c U (G + G₀)) := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, smul_smul, inv_mul_cancel₀ had, one_smul, p]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hq')

end General

end GlobalTheory.GenShift
