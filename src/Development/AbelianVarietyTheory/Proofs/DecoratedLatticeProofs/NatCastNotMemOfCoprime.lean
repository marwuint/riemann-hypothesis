import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Formalism.LocalToGlobal.Divisibility.TupUsed

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.PkOf

section Heq

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7}

theorem mu_of_heq {Bs : DefBase D.what₂.LL} {Df Df' : DefSide Bs} (h : Df = Df') {S0 : IndefData Df} {S1 : IndefData Df'}
    (hS : HEq S0 S1) : S0.μ = S1.μ := by
  subst h
  cases eq_of_heq hS
  rfl

end Heq

theorem natCast_not_mem_of_coprime {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) {n p : ℕ}
    (hc : Nat.Coprime n p) (hp : (p : 𝓞 E) ∈ PP.asIdeal) : (n : 𝓞 E) ∉ PP.asIdeal := by
  intro hn
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 E))
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hp)

theorem exists_of_mem_QE {X : Formalism.L2.Col.Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {ξ : Formalism.L2.DIV.Chr X.F X.E X.K} {PP : HeightOneSpectrum (𝓞 X.E)} (h : PP ∈ Formalism.L2.Col.QE sel ξ) : ∃ v, PP = sel v := by
  classical
  unfold Formalism.L2.Col.QE at h
  split_ifs at h with hf
  · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 h
    exact ⟨v, rfl⟩
  · simp at h

end GlobalTheory.Fam.PkOf

namespace GlobalTheory.Fam

end GlobalTheory.Fam

end
