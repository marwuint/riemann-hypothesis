import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutUnr

section Fixed
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_fixed_of_mem_biSup (ρ : Representation ℂ (GQ L n) W) (K : Set (GAf L n))
    (t : Finset (Submodule ℂ (GAf L n → W))) :
    (∀ S ∈ t, NG.IsIrrRep ρ S) → ∀ f ∈ ⨆ S ∈ t, S, f ≠ 0 → (∀ κ ∈ K, NG.rt L n κ f = f) →
      ∃ S ∈ t, ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ g = g := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf hf0 _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    exact absurd hf hf0
  | insert S t hS ih =>
    intro ht f hf hf0 hfix
    have ht' : ∀ S' ∈ t, NG.IsIrrRep ρ S' := fun S' h => ht S' (Finset.mem_insert_of_mem h)
    have hSi := ht S (Finset.mem_insert_self _ _)
    have hNst : ∀ h, ∀ g ∈ ⨆ S' ∈ t, S', NG.rt L n h g ∈ ⨆ S' ∈ t, S' := by
      intro h
      have hle : (⨆ S' ∈ t, S') ≤ (⨆ S' ∈ t, S').comap (NG.rt L n h) := by
        refine iSup₂_le fun S' hS' g hg => ?_
        exact (le_iSup₂ (f := fun (S'' : Submodule ℂ (GAf L n → W)) (_ : S'' ∈ t) => S'') S' hS')
          ((ht' S' hS').1.stable h g hg)
      exact fun g hg => hle hg
    rw [Finset.iSup_insert] at hf
    by_cases hd : S ⊓ (⨆ S' ∈ t, S') = ⊥
    · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
      have hfa : ∀ κ ∈ K, NG.rt L n κ a = a ∧ NG.rt L n κ b = b := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add] at e
        have h1 : NG.rt L n κ a - a = b - NG.rt L n κ b := by
          rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
        have hm : NG.rt L n κ a - a ∈ S ⊓ (⨆ S' ∈ t, S') :=
          ⟨S.sub_mem (hSi.1.stable κ a ha) ha, h1 ▸ Submodule.sub_mem _ hb (hNst κ b hb)⟩
        rw [hd, Submodule.mem_bot] at hm
        refine ⟨sub_eq_zero.1 hm, ?_⟩
        rw [hm] at h1
        exact (sub_eq_zero.1 h1.symm).symm
      by_cases ha0 : a = 0
      · subst ha0
        rw [zero_add] at hf0
        obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih ht' b hb hf0 fun κ hκ => (hfa κ hκ).2
        exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩
      · exact ⟨S, Finset.mem_insert_self _ _, a, ha, ha0, fun κ hκ => (hfa κ hκ).1⟩
    · have hsub : NG.IsSubrep ρ (S ⊓ (⨆ S' ∈ t, S')) :=
        ⟨inf_le_left.trans hSi.1.le, fun h g hg => ⟨hSi.1.stable h g hg.1, hNst h g hg.2⟩⟩
      have heq : S ⊓ (⨆ S' ∈ t, S') = S := (hSi.2.2 _ hsub inf_le_left).resolve_left hd
      have hSN : S ≤ ⨆ S' ∈ t, S' := heq ▸ inf_le_right
      have hfN : f ∈ ⨆ S' ∈ t, S' := (sup_le hSN le_rfl) hf
      obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih ht' f hfN hf0 hfix
      exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩

theorem exists_fixed_of_isoTyp (ρ : Representation ℂ (GQ L n) W) {S : Submodule ℂ (GAf L n → W)}
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) (K : Set (GAf L n)) {f : GAf L n → W} (hf : f ∈ NG.isoTyp ρ S)
    (hf0 : f ≠ 0) (hfix : ∀ κ ∈ K, NG.rt L n κ f = f) : ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ g = g := by
  unfold NG.isoTyp at hf
  obtain ⟨s, hs, hfs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  obtain ⟨S', hS', g, hg, hg0, hgf⟩ :=
    exists_fixed_of_mem_biSup ρ K s (fun S' h => (hs h).1) f hfs hf0 hfix
  obtain ⟨T, hT⟩ := (hs hS').2
  refine ⟨(T.symm ⟨g, hg⟩ : S), (T.symm ⟨g, hg⟩).2, ?_, fun κ hκ => ?_⟩
  · intro h0
    apply hg0
    have h1 : T.symm ⟨g, hg⟩ = 0 := Subtype.ext h0
    have h2 := congrArg T h1
    rw [LinearEquiv.apply_symm_apply, map_zero] at h2
    exact congrArg Subtype.val h2
  · set a := T.symm ⟨g, hg⟩
    have e := hT κ a ⟨NG.rt L n κ (a : GAf L n → W), hS κ _ a.2⟩ rfl
    have hTa : ((T a : _) : GAf L n → W) = g := by simp [a]
    rw [hTa, hgf κ hκ] at e
    have e2 : T ⟨NG.rt L n κ (a : GAf L n → W), hS κ _ a.2⟩ = T a := Subtype.ext (e.trans hTa.symm)
    exact congrArg Subtype.val (T.injective e2)

end Fixed

end GlobalTheory.AutUnr

namespace GlobalTheory.AutUnr

theorem mem_placesOver_of_overPl {D : D7} {p : ℕ} {w w' : PlE D.host}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hw : NG.OverPl w v) (hw' : NG.OverPl w' v)
    (h : w' ∈ placesOver D.host.E p) : w ∈ placesOver D.host.E p := by
  have h1 : ((p : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw', Ideal.mem_comap, map_natCast]; exact h
  rw [← hw, Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem exists_splitPlace_eq (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  obtain ⟨s, -, h, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw
  refine ⟨GlobalTheory.SplitConjPlace.conjSP s, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  rw [GlobalTheory.SplitConjPlace.mem_conj_w]
  refine (h x _ ?_).symm
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

end GlobalTheory.AutUnr
