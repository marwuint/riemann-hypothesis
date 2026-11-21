import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalTraceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelesCmFieldEqZeroOfComponents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecompose
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.InertFormFix.mul_idem_of_trivOutside {E : Type} [Field E] [NumberField E] [IsCMField E] (F : Subfield E)
    (hF : F = maximalRealSubfield E) (P : HeightOneSpectrum (𝓞 E))
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : NG.OverPl P v) (x : AL E)
    (hx : ∀ w, w ≠ v → compAt E w x = 0) :
    ((GlobalTheory.AdelicU.singleFin (P.under (𝓞 F)) 1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (1 : E)) *
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x := by
  subst hF
  have hvv : P.under (𝓞 (maximalRealSubfield E)) = v := HeightOneSpectrum.ext hv
  subst hvv
  have hx' : x = GlobalTheory.CongSplit.idemAt E (P.under (𝓞 (maximalRealSubfield E))) * x := by
    have h0 := GlobalTheory.AL_eq_zero_of_compAt E (x - GlobalTheory.CongSplit.idemAt E (P.under (𝓞 (maximalRealSubfield E))) * x)
      (fun w => by
        rw [RingHom.map_sub, RingHom.map_mul]
        by_cases hw : w = P.under (𝓞 (maximalRealSubfield E))
        · rw [hw, GlobalTheory.CongSplit.compAt_idemAt_self, one_mul, sub_self]
        · rw [GlobalTheory.CongSplit.compAt_idemAt_ne E _ hw, hx w hw, zero_mul, sub_zero])
    exact (sub_eq_zero.1 h0)
  conv_rhs => rw [hx']
  rw [RingEquiv.map_mul]
  congr 1

theorem GlobalTheory.InertFormFix.finPart_mul_of_trivOutside : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D), Formalism.IndefR.Mult.IsPrimeIdem P e f → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl P v → ∀ x : AL D.host.E, (∀ w, w ≠ v → compAt D.host.E w x = 0) → Formalism.L2.Theta.finPart D f * (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x := by
  intro D hF P e f hP v hv x hx
  have hf := GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hP rfl
  subst hf
  exact GlobalTheory.InertFormFix.mul_idem_of_trivOutside D.host.F hF P v hv x hx

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.InertFormFix.suppF_of_trivOutside : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (Q : Formalism.IndefR.principalLevelFrame.RowPsi V n), Formalism.IndefR.principalLevelFrame.StdPsi hF Q → ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D), Formalism.IndefR.Mult.IsPrimeIdem P e f → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl P v → ∀ κ : GAf D.host.E n, TrivOutside {v} κ → Formalism.IndefR.Mult.SuppF V f (Q.ψ κ) := by
  intro D hF V n Q hQ P e f hP v hv κ hT
  obtain ⟨⟨β, β', hββ', hβ'β, hmat⟩, -⟩ := hQ
  rw [GlobalTheory.SphTrans.suppF_iff f (Q.into κ), hmat κ]
  have hT' : ∀ w, w ≠ v → (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (compAt D.host.E w) = 1 :=
    fun w hw => hT w (by simpa using hw)
  change Formalism.L2.Theta.finPart D f • (β * (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm * β' - 1) = β * (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm * β' - 1
  set M : Matrix (Fin n) (Fin n) (AL D.host.E) := κ.1.1 with hMdef
  set K := M.map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm with hKdef
  have hcore : ∀ a b, Formalism.L2.Theta.finPart D f * (K - 1) a b = (K - 1) a b := by
    intro a b
    have hx : ∀ w, w ≠ v → compAt D.host.E w (M a b - (1 : Matrix (Fin n) (Fin n) (AL D.host.E)) a b) = 0 := by
      intro w hw
      have h1 := congrFun (congrFun (hT' w hw) a) b
      rw [Matrix.map_apply] at h1
      rw [RingHom.map_sub, h1]
      by_cases hab : a = b
      · rw [hab, Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, sub_self]
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, RingHom.map_zero, sub_zero]
    have h2 := GlobalTheory.InertFormFix.finPart_mul_of_trivOutside D hF P e f hP v hv _ hx
    have e3 : (K - 1) a b = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm (M a b -
        (1 : Matrix (Fin n) (Fin n) (AL D.host.E)) a b) := by
      rw [Matrix.sub_apply, hKdef, Matrix.map_apply, RingEquiv.map_sub]
      by_cases hab : a = b
      · rw [hab, Matrix.one_apply_eq, Matrix.one_apply_eq, RingEquiv.map_one]
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, RingEquiv.map_zero]
    rw [e3, h2]
  have hK : Formalism.L2.Theta.finPart D f • (K - 1) = K - 1 := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul, hcore]
  have e1 : β * K * β' - 1 = β * (K - 1) * β' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hββ']
  rw [e1]
  conv_rhs => rw [← hK]
  rw [Matrix.mul_smul, Matrix.smul_mul]

end
