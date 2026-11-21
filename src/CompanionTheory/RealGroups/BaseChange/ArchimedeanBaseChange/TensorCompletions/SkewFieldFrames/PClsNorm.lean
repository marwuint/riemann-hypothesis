import Mathlib
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.Imports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDetUnitAndTwist

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3.ClsNormP

theorem thetaGL_val' {k : Type} [CommRing k] (n : ℕ) (c : k →+* k) (g : GL (Fin n) k) :
    (thetaGL n c g).val = GlobalTheory.Tw.Phi n k * ((g⁻¹).val.map c)ᵀ * (GlobalTheory.Tw.Phi n k)ᵀ := rfl

theorem units_map_val {k : Type} [Field k] {n : ℕ} {B : Type} [CommRing B]
    (ρ : B →+* Matrix (Fin n) (Fin n) k) (t : Bˣ) : (Units.map ρ.toMonoidHom t).val = ρ t := rfl

end CompanionTheory.Rg.BcB.G3.ClsNormP

namespace CompanionTheory.Rg.BcB.G3

end CompanionTheory.Rg.BcB.G3

end
