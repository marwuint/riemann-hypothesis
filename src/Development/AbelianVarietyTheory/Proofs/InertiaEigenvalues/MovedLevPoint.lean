import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicMatrixMemLatticeOfColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ReducedBasisStatement

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

set_option maxHeartbeats 1600000

namespace GlobalTheory.SingleDatum.MovedLevel

theorem cSep_mem {D : D7} {H : Geo.Tor.Host D.host.E} (l : Geo.Tor.Level H) :
    cSep l ∈ Mfr l ∧ cSep l - 1 ∈ l.Mb := by
  have hex : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := by
    have : (1 : 𝓞 D.host.E) ∈ l.Mb ⊔ Mfr l := by rw [show l.Mb ⊔ Mfr l = ⊤ from l.coprime]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 this
    exact ⟨y, hy, by rw [← hxy, sub_add_cancel_right]; exact neg_mem hx⟩
  unfold cSep; rw [dif_pos hex]; exact hex.choose_spec

end GlobalTheory.SingleDatum.MovedLevel
