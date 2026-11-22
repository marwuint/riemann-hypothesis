import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag

noncomputable section

namespace GlobalTheory.IwArchMin

open Matrix

section Alg

variable {A : Type} [CommRing A] {n : ℕ}

def toC (e : A ≃+* ℂ) (b : GL (Fin n) A) : (Fin n → A) →ₛₗ[(e : A →+* ℂ)] (Fin n → ℂ) where
  toFun y := fun r => e (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) r)
  map_add' y z := by funext r; simp [Matrix.mulVec_add]
  map_smul' c y := by funext r; simp [Matrix.mulVec_smul]

theorem toC_apply (e : A ≃+* ℂ) (b : GL (Fin n) A) (y : Fin n → A) (r : Fin n) :
    toC e b y r = e (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) r) := rfl

end Alg

end GlobalTheory.IwArchMin

namespace GlobalTheory.IwArchMin

end GlobalTheory.IwArchMin

namespace GlobalTheory.IwArchMin

end GlobalTheory.IwArchMin

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory.IwArchMin

end GlobalTheory.IwArchMin
