import Formalism.SharpRestriction.InertJacobiLevels.VVEqEmptyOfNotIsResidueClassZero
import Formalism.SharpRestriction.ParConsts

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField IsDedekindDomain

section Drop

variable {D : D7} (L0 : SizeData₂ D) (X0 : G.Inst D L0) (K : G.Consts) (Cr : ℝ)
  (len : D.what₂.Word → D.what₂.places.Pl → ℚ) (hw : 1 ≤ L0.sc.w'' D.R.n)
  (hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i)))
  (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0)

def tieL : SizeData₂ D := tieWeightData L0 X0 K {p | NoGain X0 K Cr p} len hw hg hu

def tieX : G.Inst D (tieL L0 X0 K Cr len hw hg hu) := tieInst L0 X0 K {p | NoGain X0 K Cr p} len hw hg hu

theorem tieL_drop_iff (p : ℕ) :
    p ∈ (tieL L0 X0 K Cr len hw hg hu).drop ↔
      NoGain (tieX L0 X0 K Cr len hw hg hu) K Cr p ∧ ∀ u, p ≠ (D.mem u).A.T :=
  Iff.rfl

end Drop

structure FieldData where
  φ : Formalism.HC.Frame
  E : Type
  [fld : Field E]
  [nf : NumberField E]
  gal : (E ≃ₐ[ℚ] E) ≃* φ.GG
  N : ℕ
  ζ : CyclotomicField N ℚ
  a : E
  b : E

attribute [instance] FieldData.fld FieldData.nf

def FieldData.hval (F : FieldData) (p : ℕ) : ℕ :=
  (F.φ.iotaInv (Classical.epsilon (fun g : F.φ.GG =>
    ∃ (P : Ideal (𝓞 F.E)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)}))
      (σ : F.E ≃ₐ[ℚ] F.E), IsArithFrobAt ℤ σ P ∧ F.gal σ = g)).2).val

def fieldDataH (x : Σ R : Ranks, Host R) : FieldData :=
  ⟨x.1.toFrame, x.2.E, x.2.gal, x.2.condN, x.2.cycZeta, x.2.sqq, x.2.sqd⟩

def fieldData (D : D7) : FieldData := fieldDataH ⟨D.R, D.host⟩

theorem hP_val (D : D7) (p : ℕ) : (G.hP D p).val = (fieldData D).hval p := rfl

end Formalism.MainNotions.Inhab

end
