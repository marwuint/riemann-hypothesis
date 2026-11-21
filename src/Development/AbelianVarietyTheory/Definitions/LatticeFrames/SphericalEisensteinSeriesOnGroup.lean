import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch

variable {D : D7}

structure Lvl (V : HSp D) where

  L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

  c : GL (Fin V.rank) (AE D)

def Lvl.K {V : HSp D} (l : Lvl V) : Subgroup (GA D V) := levelAll D.sp.cm.sig V.gram l.L l.c

def Lvl.Good {V : HSp D} (l : Lvl V) : Prop :=
  Submodule.IsLattice D.host.E l.L ∧ (∀ v, IsSelfDualAt D.sp.cm.sig V.gram l.L v) ∧ IsMaj V l.c

def Lvl.form {V : HSp D} (l : Lvl V) : Mx D V.rank V.rank := adj (l.c⁻¹).1 ⬝ (l.c⁻¹).1

theorem Lvl.K_frameLat (V : HSp D) (a : GL (Fin V.rank) (AE D)) : Lvl.K (⟨frameLat V, a⟩ : Lvl V) = Kmax V a := rfl

theorem Lvl.Good.isCompact_K {V : HSp D} {l : Lvl V} (h : l.Good) : IsCompact (l.K : Set (GA D V)) :=
  haveI := h.1
  isCompact_levelAll (isCMExt_host D) _ _ _

section SlopeTestRemainingChoices

variable {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (K : Subgroup (GA D T))

def sphericalSectionIwasawa (s : ℂ) : GA D T → ℂ := fun h => npow (iwAbs (absDet d) K h) (s + rhoH T r)

def sphericalEisensteinSeriesOnGroup (h : GA D T) : ℂ → ℂ := fun s => cosetSum (stab d) (GQ T) (sphericalSectionIwasawa d K s) h

theorem sphericalSection_maximalCompact (b : GL (Fin T.rank) (AE D)) : sphericalSectionIwasawa d (Kmax T b) = sphericalSection d b := rfl

end SlopeTestRemainingChoices

section Ops

variable {n : ℕ}

def projS {T : HSp D} {K : Subgroup (GA D T)} (ν : Measure K) (Φ : Mx D T.rank n → ℂ) : Mx D T.rank n → ℂ :=
  fun x => ∫ k, Φ (mt T (k : GA D T)⁻¹ ⬝ x) ∂ν

def ikS {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) (μ : Measure (Mx D t n)) (Φ : Mx D T.rank n → ℂ) : Mx D T'.rank n → ℂ :=
  fun a => ∫ x, Φ (d.jX ⬝ x + d.j0 ⬝ a) ∂μ

variable (θ : InfFam D) (τ : D.what₂.Tau)

variable {θ} {V V₀ : HSp D} {r : ℕ} (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n))

variable (d : HypDec V V₀ r) (K : Subgroup (GA D V))

end Ops

end GlobalTheory.RegSch

end
