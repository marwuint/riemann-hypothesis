import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section
namespace GlobalTheory.GammaAct

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def wittEquiv (G : PreTilt O p ≃+* PreTilt O p) : Ainf p O ≃+* Ainf p O :=
  RingEquiv.ofRingHom (WittVector.map (G : PreTilt O p →+* PreTilt O p))
    (WittVector.map (G.symm : PreTilt O p →+* PreTilt O p))
    (by ext x n; simp [WittVector.map_coeff])
    (by ext x n; simp [WittVector.map_coeff])

theorem wittEquiv_apply (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) :
    wittEquiv G a = WittVector.map (G : PreTilt O p →+* PreTilt O p) a := rfl

theorem wittEquiv_ofPadic (G : PreTilt O p ≃+* PreTilt O p) (x : ℤ_[p]) :
    wittEquiv G (ofPadic p O x) = ofPadic p O x := by
  rw [wittEquiv_apply, ofPadic, RingHom.comp_apply]
  generalize (WittVector.equiv p).symm.toRingHom x = y
  ext n
  simp only [WittVector.map_coeff]
  exact congrArg (fun f : ZMod p →+* PreTilt O p => f (y.coeff n))
    (RingHom.ext_zmod ((G : PreTilt O p →+* PreTilt O p).comp (ZMod.castHom (dvd_refl p) _)) _)

end GlobalTheory.GammaAct

namespace GlobalTheory.GammaAct

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def wittAlgEquiv (G : PreTilt O p ≃+* PreTilt O p) : Ainf p O ≃ₐ[ℤ_[p]] Ainf p O :=
  AlgEquiv.ofRingEquiv (f := wittEquiv G) (fun x => wittEquiv_ofPadic G x)

variable (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]

def tensorEquiv (G : PreTilt O p ≃+* PreTilt O p) : RL p O Λ ≃+* RL p O Λ :=
  (Algebra.TensorProduct.congr (wittAlgEquiv G) (AlgEquiv.refl : Λ ≃ₐ[ℤ_[p]] Λ)).toRingEquiv

theorem tensorEquiv_tmul (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) (l : Λ) :
    tensorEquiv Λ G (a ⊗ₜ l) = wittEquiv G a ⊗ₜ l := rfl

theorem tensorEquiv_symm_tmul (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) (l : Λ) :
    (tensorEquiv Λ G).symm (a ⊗ₜ l) = (wittEquiv G).symm a ⊗ₜ l := rfl

end GlobalTheory.GammaAct

namespace GlobalTheory.GammaAct

section
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem tensorEquiv_inA (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]
    (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) :
    tensorEquiv Λ G (inA a) = inA (wittEquiv G a) := rfl

end

end GlobalTheory.GammaAct
