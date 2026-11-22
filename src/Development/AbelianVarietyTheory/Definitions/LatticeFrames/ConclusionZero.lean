import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SiegelWeilFock
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVector
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramAtP

noncomputable section
namespace GlobalTheory.Core.Rk.IP.FockModel
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem resEta_one_dbl (A : HSp D) {χ : (AE D)ˣ →* Circle} {k : ℕ} (hr : ResEta D χ k) : ResEta D 1 (dblSp A).rank :=
  ⟨hr.1, fun e he a => by
    have h4 := he.2.2.1 (idF D a)
    have h5 : Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := Units.ext (by
      change Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) a.1) = _
      have := t2Space_adeleRing' (F := D.host.F)
      have : Nontrivial (AF D.host.F) :=
        (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers D.host.F) D.host.F).nontrivial
      rw [Algebra.norm_algebraMap, Module.finrank_baseChange, D.sp.cm.deg2, Units.val_pow_eq_pow_val])
    rw [h5, map_pow] at h4
    change (1 : Circle) = e a ^ (A.rank + A.rank)
    rw [← two_mul, pow_mul, h4, one_pow]⟩

end GlobalTheory.Core.Rk.IP.FockModel

end
