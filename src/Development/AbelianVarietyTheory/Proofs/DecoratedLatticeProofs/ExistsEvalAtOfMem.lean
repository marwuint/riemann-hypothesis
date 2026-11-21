import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.CapelliUniv

open Formalism.REAL GlobalTheory.SmoothForms

section Transport

variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ}

theorem qdet_map (f : A →ₐ[ℂ] B) (E : Fin n → Fin n → A) (u : ℂ) :
    Formalism.REAL.qdet (fun a b => f (E a b)) u = f (Formalism.REAL.qdet E u) := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod,
    List.map_ofFn, Function.comp_def, map_add, AlgHom.commutes, apply_ite f, map_zero]

end Transport

end GlobalTheory.CapelliUniv

namespace GlobalTheory.CapelliUniv

end GlobalTheory.CapelliUniv

namespace GlobalTheory.CapelliUniv

end GlobalTheory.CapelliUniv

namespace GlobalTheory.CapelliUniv

end GlobalTheory.CapelliUniv
