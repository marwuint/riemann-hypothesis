import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmplePullbackPowerDivOfLocallyAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BorelWeilFlagModelDetInverseIsAmpleLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightSectionsNonvanishingOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsNsmulOfCommon

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem _root_.GlobalTheory.HSApp.exists_dominant_sub {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
    (la ν : _root_.GlobalTheory.AllWt.Weight Dw) (hla : _root_.GlobalTheory.HSApp.GapGe (1 : ℤ) la) :
    ∃ mu : _root_.GlobalTheory.AllWt.Weight Dw, _root_.GlobalTheory.HSApp.GapGe (0 : ℤ) mu ∧
      ∃ m : ℕ, 0 < m ∧ m • la - mu = ν := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ τ : _root_.GlobalTheory.AllWt.Psi H, ∀ k : ℕ,
      k + 1 < Dw.p + Dw.q → _root_.GlobalTheory.CompHS.gap (ν τ) k ≤ M := by
    refine ⟨Finset.univ.sup fun p : _root_.GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q) =>
      (_root_.GlobalTheory.CompHS.gap (ν p.1) (p.2 : ℕ)).toNat, fun τ k hk => ?_⟩
    have h := Finset.le_sup (f := fun p : _root_.GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q) =>
      (_root_.GlobalTheory.CompHS.gap (ν p.1) (p.2 : ℕ)).toNat)
      (Finset.mem_univ (τ, (⟨k, by omega⟩ : Fin (Dw.p + Dw.q))))
    exact (Int.self_le_toNat _).trans (by exact_mod_cast h)
  refine ⟨(M + 1) • la - ν, ?_, M + 1, Nat.succ_pos M, sub_sub_cancel _ _⟩
  unfold _root_.GlobalTheory.HSApp.GapGe at hla ⊢
  intro τ k hk
  have h₁ := hla τ k hk
  have h₂ := hM τ k hk
  unfold _root_.GlobalTheory.CompHS.gap at h₁ h₂ ⊢
  rw [dif_pos hk] at h₁ h₂ ⊢
  have e : ∀ i, ((M + 1) • la - ν) τ i = ((M + 1 : ℕ) : ℤ) * la τ i - ν τ i := by
    intro i
    simp
  rw [e, e]
  push_cast
  nlinarith

end GlobalTheory.HSApp
