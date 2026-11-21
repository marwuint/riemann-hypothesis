import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawOfSquaresSelfDualSplitLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharOnIdMulSqrtAbsNormInvMemSubringStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterUnramifiedOffBad
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElemStdLatticeSandwichSplitSupport

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ClassScalarIn

theorem unimod_hLat {D : D7} (V : HSp D) (hg : V.gram = 1) (g : Bridge.Gf V) :
    (⟨Bridge.hLat V g⟩ : GenLat D.host.E V.rank).Unimod := by
  intro v
  have h := (GlobalTheory.MovedLat.isSelfDualC_hLat V g).2 v
  rw [h]
  refine forall_congr' fun w => imp_congr_right fun _ => ?_
  simp only [hg, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have e : ∑ j, (IsCMField.complexConj D.host.E) (v j) * w j =
      IsCMField.complexConj D.host.E (∑ x, star (w x) * v x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, show star (w x) = IsCMField.complexConj D.host.E (w x) from rfl,
      IsCMField.complexConj_apply_apply, mul_comm]
  rw [e]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨(Formalism.L2.Pj.hostOfRecord D).bar b, by rw [← hb]; exact (Formalism.L2.Pj.hostOfRecord D).bar_eq b⟩
  · rintro ⟨b, hb⟩
    refine ⟨(Formalism.L2.Pj.hostOfRecord D).bar b, ?_⟩
    rw [(Formalism.L2.Pj.hostOfRecord D).bar_eq]
    have hb' : ((b : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (∑ x, star (w x) * v x) := hb
    rw [hb', IsCMField.complexConj_apply_apply]

theorem sqrt_pow_odd (N k s : ℕ) : Real.sqrt (((N * k ^ 2 : ℕ) : ℝ) ^ (2 * s + 1)) =
    ((N ^ s * k ^ (2 * s + 1) : ℕ) : ℝ) * Real.sqrt N := by
  rw [show (((N * k ^ 2 : ℕ) : ℝ)) ^ (2 * s + 1) = (((N ^ s * k ^ (2 * s + 1) : ℕ) : ℝ)) ^ 2 * N by push_cast; ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

end GlobalTheory.ClassScalarIn

