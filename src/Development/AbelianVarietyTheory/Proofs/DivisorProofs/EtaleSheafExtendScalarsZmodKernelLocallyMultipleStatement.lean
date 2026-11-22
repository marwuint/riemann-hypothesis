import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafExtendScalarsZmodKernelLocallyMultiple

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafExtendScalars_zmod_kernel_locally_multiple : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0}) (x : Sec M U), extSh.sec (ZMod.castHom hq (ZMod q)) M U x = 0 → Loc U fun V g => ∃ y : Sec M V, Sec.res g x = q • y := GlobalTheory.EtC.extSh_sec_eq_zero_loc
