import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LinearCoefficientData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceOffLevelSetProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOperatorsCommOfAntiInvolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalCoefficientElementarySymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalFunctionDualLabel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDivisorDualLabel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyScaledInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedConjugatePlaceUniformiserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularWeightsOfGapTwo

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta
open Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Polynomial GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem GlobalTheory.HeckeParts
open Formalism.IndefR.Bridge (SplitOff)
open scoped TensorProduct

namespace GlobalTheory.SphPar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Par

open Formalism.UG

theorem exists_enum {n : ℕ} {s : Multiset ℂ} (h : s.card = n) : ∃ α : Fin n → ℂ, Finset.univ.val.map α = s := by
  induction s using Quotient.inductionOn with
  | h l =>
    have hl : l.length = n := by simpa using h
    subst hl
    refine ⟨l.get, ?_⟩
    rw [Fin.univ_val_map, List.ofFn_get]
    rfl

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} {lab lab' : List ℤ → Prop}
  {c c' : List ℤ → ℂ} {s : Multiset ℂ}

theorem ParGL.eq (h : ParGL P n lab c s) (h' : ParGL P n lab c' s) {d : List ℤ} (hd : lab d) : c d = c' d := by
  obtain ⟨α, hα⟩ := exists_enum h.1
  obtain ⟨φ, h1, h2, -⟩ := Formalism.UG.Final.SphericalExists E P n α fun i e =>
    h.2.1 (hα ▸ Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, e⟩)
  have := (h.2.2 α hα φ h1 d hd).symm.trans (h'.2.2 α hα φ h1 d hd)
  rwa [h2, mul_one, mul_one] at this

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q : ℕ}

theorem ParU.eq [CompleteSpace L] (hU : IsUnramInv ϖ σ q) (h : ParU σ q n lab c s) (h' : ParU σ q n lab c' s) {d : List ℤ}
    (hd : lab d) : c d = c' d := by
  obtain ⟨α, hα⟩ := h.2.1
  obtain ⟨φ, h1, h2, -⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega) α fun i e =>
    h.1 (hα ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, e⟩)))))
  have := (h.2.2 α hα φ h1 d hd).symm.trans (h'.2.2 α hα φ h1 d hd)
  rwa [h2, mul_one, mul_one] at this

end U

variable [StarRing E]

end Par

theorem IsPar.eq {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ} {lab : List ℤ → Prop} {c c' : List ℤ → ℂ}
    {s : Multiset ℂ} (h : IsPar P n lab c s) (h' : IsPar P n lab c' s) {d : List ℤ} (hd : lab d) : c d = c' d := by
  by_cases hP : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal
  · obtain ⟨σ, ϖ, q, h1, h2⟩ := GlobalTheory.T.unramified_conjugate_place_uniformiser P hP
    exact (h.2 hP σ ϖ q h1 h2).eq h2 (h'.2 hP σ ϖ q h1 h2) hd
  · exact (h.1 hP).eq (h'.1 hP) hd

end GlobalTheory.SphPar

end
