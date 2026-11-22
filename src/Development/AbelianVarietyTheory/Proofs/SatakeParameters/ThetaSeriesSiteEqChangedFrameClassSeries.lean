import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesPairOfPullbackKernelFunction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DecompositionUnitaryMulStarEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleKernelEqSmulPullbackClassKernel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackScalarNeZeroLatticeTuplePair
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelB.serAt_all : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j < D.R.m, d.SerAt S ι j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPair hPos d ι hι j hj La La' hLa hLa'
  have hr := _root_.GlobalTheory.TwV.DelB.sysS_ranks S
  have hu := _root_.GlobalTheory.TwV.DelB.Dec.eM_mul_star S d
  have hp := _root_.GlobalTheory.TwV.DelB.pullAt_of_dict S hDict d j hj La La' hLa hLa'
  have hs := _root_.GlobalTheory.TwV.DelB.pullbackScalar_ne_zero S d j hj La La' hLa hLa'
  exact _root_.GlobalTheory.TwV.DelB.frecG_pull D _ (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) S.lam ι hι (J.rho std) hPos d.eM
    (ltC S.g S.hLT) j La La' (hu j La) (hu (j + 1) La') t.B t.χ (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT hPair
    (hr.1 ▸ hj) hLa hLa' (d.sP S j La La') (thCl (X := sysS H X std) t u μ (clsAt X H) j La La') hs hp
