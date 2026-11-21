import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationOfHyp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound

open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN

theorem satake_window (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (P : CuspSub E a) (hP : P.IsCsd)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (hσ : P.IsLocComp w σ)
    (S : Multiset ℂˣ) (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) : ∀ s ∈ S,
      (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) < ‖(s : ℂ)‖ ∧ ‖(s : ℂ)‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ) :=
  PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound E a (CG.mk P) (GlobalTheory.CuspRep.CsdUnitary.isUnitary_of_isCsd E a (CG.mk P) hP) w S
    ((GlobalTheory.BcSpehCompare.hasSat_iff hσ S).2 hS)

theorem string_forces_long_part : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (c : ℕ) (d : Fin c → ℕ)
    (S : Fin c → Multiset ℂˣ) (T : Multiset ℂˣ) (t : ℕ) (ν : ℂ),
  1 ≤ t → (∀ i, ∀ s ∈ S i, ‖(s : ℂ)‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ)) → ‖ν‖ = 1 →
  ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
    T.map (fun z => (z : ℂ)) →
  (Multiset.range t).map (fun c : ℕ => ν * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((t : ℂ) - 1) / 2 - c)) ≤
    T.map (fun z => (z : ℂ)) →
  ∃ i, t ≤ d i := by
  intro E _ _ w c d S T t ν ht hS hν hsum hle
  have hN1 : 1 < Ideal.absNorm w.asIdeal := by
    have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
    have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
    omega
  set N := Ideal.absNorm w.asIdeal with hN
  have hmem : ν * ((N : ℕ) : ℂ) ^ (((t : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) ∈ T.map (fun z => (z : ℂ)) :=
    Multiset.mem_of_le hle (Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 (by omega), rfl⟩)
  rw [← hsum] at hmem
  obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 hmem
  obtain ⟨k, -, hk⟩ := Multiset.mem_sum.1 hi
  obtain ⟨s, hs, hsk⟩ := Multiset.mem_map.1 hk
  have hs1 : ‖s‖ < (N : ℝ) ^ (1 / 2 : ℝ) := by
    simp only [Multiset.bind_def, Multiset.pure_def, Multiset.mem_bind, Multiset.mem_singleton] at hs
    obtain ⟨u, hu, rfl⟩ := hs
    exact hS i u hu
  have hNpos : 0 < N := by omega
  have hn := congrArg (fun z : ℂ => ‖z‖) hsk
  simp only [norm_mul, hν, one_mul, Complex.norm_natCast_cpow_of_pos hNpos] at hn
  have hre : ((((d i : ℂ) - 1) / 2 - ((k : ℕ) : ℂ))).re = ((d i : ℝ) - 1) / 2 - (k : ℕ) := by simp
  have hre2 : ((((t : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))).re = ((t : ℝ) - 1) / 2 := by simp
  rw [hre, hre2] at hn
  have hN1' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hlt : (N : ℝ) ^ (((t : ℝ) - 1) / 2) < (N : ℝ) ^ ((1 / 2 : ℝ) + (((d i : ℝ) - 1) / 2 - (k : ℕ))) := by
    rw [Real.rpow_add hN0, ← hn]
    exact mul_lt_mul_of_pos_right hs1 (Real.rpow_pos_of_pos hN0 _)
  have hle' := (Real.rpow_lt_rpow_left_iff hN1').1 hlt
  have hk' : ((k : ℕ) : ℝ) ≥ 0 := by positivity
  refine ⟨i, ?_⟩
  have : (t : ℝ) < d i + 1 := by linarith
  have : t < d i + 1 := by exact_mod_cast this
  omega

end UpperTheory.GalN
