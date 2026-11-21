import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Ideal

theorem localMult_ne_zero_of_mem_minimalPrimes {A : Type*} [CommRing A] [IsNoetherianRing A]
    {J P : Ideal A} (hP : P ∈ J.minimalPrimes) : localMult J P ≠ 0 := by
  have hPp : P.IsPrime := hP.1.1
  unfold localMult
  rw [dif_pos hPp]
  let R := Localization.AtPrime P
  let I : Ideal R := J.map (algebraMap A R)
  have hmin : IsLocalRing.maximalIdeal R ∈ I.minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map P.primeCompl R J, Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal]
    exact hP
  have := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmin
  have : IsArtinian R (R ⧸ I) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  have : IsNoetherian R (R ⧸ I) := isNoetherian_quotient I
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hmin.1.2
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  rw [Ne, ENat.toNat_eq_zero, not_or]
  exact ⟨(Module.length_pos (R := R) (M := R ⧸ I)).ne', Module.length_ne_top⟩

end GroundTheory.Heights₂.Heights
