import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.IsMultiHomogOfIsChowForm

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

namespace VerticalPartMultiplicity

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)

theorem length_localizedModule_quotient {A : Type*} [CommRing A] (K W : Ideal A) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ K)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) := by
  let g := Submodule.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
    (Algebra.linearMap A (Localization.AtPrime W)) K
  let e := (IsLocalizedModule.linearEquiv W.primeCompl g
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ K))).restrictScalars (Localization.AtPrime W)
  have hK : Submodule.localized' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)) K = K.map (algebraMap A (Localization.AtPrime W)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  rw [← e.length_eq]
  exact (Submodule.quotEquivOfEq _ _ hK).length_eq

theorem length_self_eq_of_ringEquiv {Q Q' : Type*} [CommRing Q] [CommRing Q'] (τ : Q ≃+* Q') :
    Module.length Q Q = Module.length Q' Q' := by
  letI := RingHomInvPair.of_ringEquiv τ
  letI := RingHomInvPair.symm (↑τ : Q →+* Q') (τ.symm : Q' →+* Q)
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap τ.toSemilinearEquiv)]

variable {n : ℕ}

def eb (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟩, i⟩
    rfl

abbrev ι : ℤ ≃+* 𝓞 ℚ := Rat.ringOfIntegersEquiv.symm

def Ψ (n : ℕ) : MRing (PBlk n) ≃+* MvPolynomial (Fin n) (𝓞 ℚ) :=
  (renameEquiv ℤ (eb n)).symm.toRingEquiv.trans (mapEquiv (Fin n) ι)

theorem Ψ_apply (f : MRing (PBlk n)) :
    Ψ n f = MvPolynomial.map (ι : ℤ →+* 𝓞 ℚ) (rename (eb n).symm f) := rfl

end VerticalPartMultiplicity

end ObjectsChow

end GroundTheory.Heights₂.Heights
