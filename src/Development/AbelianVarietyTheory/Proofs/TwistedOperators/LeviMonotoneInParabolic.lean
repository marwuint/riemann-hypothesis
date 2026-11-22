import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section
open scoped TensorProduct Classical

namespace GlobalTheory.LeviSign

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab)

section Ops

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) {V : HSpace E} (Φ : WittFrame V) (R : Type) [CommRing R] [Algebra F R]

def cf (v : V.V) : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun y := hLin hc.sig V.gram R y (coordR V R v)
  map_add' y y' := hLin_add_left _ _ _ y y' _
  map_smul' c y := hLin_smul_left _ _ _ c y _

theorem cf_apply (v : V.V) (y : Fin V.rank → R ⊗[F] E) : cf hc R v y = hR R hc.sig V.gram (coordR V R v) y := rfl

variable {hc Φ R}

end Ops

section Levi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {V : HSpace E} {Φ : WittFrame V} {R : Type} [CommRing R] [Algebra F R]

variable (hc R) in

def Ag (g : HA R hc.sig V.gram) : Module.End (R ⊗[F] E) (Fin V.rank → R ⊗[F] E) :=
  (HA.mat R hc.sig V.gram g).1.mulVecLin

end Levi

end GlobalTheory.LeviSign
