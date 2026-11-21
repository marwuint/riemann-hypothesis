import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweQuotientFiniteLengthFockPolynomials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthTensorProductFactors
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory
theorem howeAlg_fock_tensor : ∀ (T : Type) [Fintype T] [DecidableEq T] (P Q R S : T → ℕ) (x : T → ℂ), HoweAlg (fun w => actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (tensAny fun w => coinv (P w) (Q w) (R w) (S w) (x w)) := by
  intro T _ _ P Q R S x
  exact _root_.GlobalTheory.HoweR.howeAlg_tensAny T (fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) _ _ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) (fun w => coinv (P w) (Q w) (R w) (S w) (x w)) (fun w => _root_.GlobalTheory.HoweR.fock_pack (P w) (Q w) (R w) (S w) (x w))
end GlobalTheory
