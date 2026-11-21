import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.RecLevelLocF

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.UG.P

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

variable (h : BasePi ST π)

def fvPsiEquiv {P : Pl E} (hP : P ∈ ST) (hov : IsOver v P) (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P) :
    fMod hc n ST v ≃+ kP P :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
    ext x
    rw [AddMonoidHom.mem_ker, rll_psi_ker hc n v h hP huniq]
    rfl : ((Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseKer E n ST)).comap
      (baseDualV hc n ST v).subtype).toAddSubgroup = (rll_psi hc n v h P).ker)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (rll_psi_surj hc n v h hov))

def fvMulEquiv {R : Type} [CommRing R] (a b : R) (hab : a * b = 1) : R ≃+ R where
  toFun x := a * x
  invFun x := b * x
  left_inv x := by
    show b * (a * x) = x
    rw [← mul_assoc, mul_comm b a, hab, one_mul]
  right_inv x := by
    show a * (b * x) = x
    rw [← mul_assoc, hab, one_mul]
  map_add' := mul_add _

def fvMeL {P : Pl E} (hP : P ∈ ST) (hov : IsOver v P) (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P)
    (a b : 𝓞 E ⧸ P.asIdeal) (hab : a * b = 1) : fMod hc n ST v ≃+ (𝓞 E ⧸ P.asIdeal) :=
  (fvPsiEquiv hc n v h hP hov huniq).trans (fvMulEquiv a b hab)

theorem fvMeL_fLoc {P : Pl E} (hP : P ∈ ST) (hov : IsOver v P) (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P)
    (a b : 𝓞 E ⧸ P.asIdeal) (hab : a * b = 1) (x : baseDualV hc n ST v) :
    fvMeL hc n v h hP hov huniq a b hab (fLoc hc n ST v x) = a * rll_psi hc n v h P x := rfl

variable (SG : Finset (Pl E)) (c₀ : DiaG E ST)

end Loc

end Formalism.L2.Col
