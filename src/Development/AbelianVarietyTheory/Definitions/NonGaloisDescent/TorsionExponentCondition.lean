import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open Classical

namespace GlobalTheory.HubX.Check

variable {D : D7}

variable {L : SizeData₂ D} {HW : HWOf D.loc} {R : KillingConditions.RowK} {X : KillingConditions.HubData D}

theorem not_inert {l : ℕ} (h1 : TwistedPlaces.SplitK D l) : ¬ TwistedPlaces.InertK D l := by
  intro h2
  unfold TwistedPlaces.SplitK at h1
  unfold TwistedPlaces.InertK at h2
  rw [h1] at h2
  rcases h2 with h2 | h2 <;> cases h2

theorem decl (h : Canon L HW R X) (hJ : AdmissibleParameterJ.ConclusionJa D) (i : D.nd.Loc) (hg : D.nd.l i ∉ TwistedPlaces.gset D)
    (hr : KillingConditions.RangeAD L X.exc (D.nd.l i)) (hs : TwistedPlaces.SplitK D (D.nd.l i))
    (hex : ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc hJ.choose) : EmbeddingTypes.hypDecl i (X.dc i) hJ.choose := by
  have hp := (D.nd.lPrime i).out
  have h5 : 5 ≤ D.nd.l i := by
    have h2 := hp.two_le
    have h3 : D.nd.l i ≠ 3 := fun e => hr.1 (Or.inr e)
    have h2' : D.nd.l i ≠ 2 := fun e => hr.1 (Or.inl (e ▸ D.host.toHostRaw.two_mem_small))
    have h4 : D.nd.l i ≠ 4 := fun e => by rw [e] at hp; norm_num at hp
    omega
  have hsp : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) := by
    refine ⟨hp, h5, fun e => hr.2.1 (Or.inl e), fun e => hr.2.1 (Or.inr e), fun k e => hg ?_, hs⟩
    rw [e]
    fin_cases k <;> simp [TwistedPlaces.gset]
  have he : epJ D = hJ.choose := epJ_eq hJ
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) ∧ ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc (epJ D) :=
    ⟨hsp, by rw [he]; exact hex⟩
  rw [h.dc i (not_inert hs), dcOf, dif_pos hc, ← he]
  exact hc.2.choose_spec

end GlobalTheory.HubX.Check

end
