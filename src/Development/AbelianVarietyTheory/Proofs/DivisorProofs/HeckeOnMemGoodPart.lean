import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMultMapRightTranslateFiniteAdelicNormalizer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsDCOfMemDoubleCoset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiInvolutionOfChars
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSumFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeInnerProductModel

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Bridge Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.HeckeModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Group

variable {G : Type} [Group G]

theorem sum_eq_of_isDC {J : Subgroup G} {x x' : G} {A A' : Finset G} {F : G → ℂ} (hA : IsDC J x A) (hA' : IsDC J x' A')
    (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂) (hF : ∀ k ∈ J, ∀ h, F (h * k) = F h) (h : G) :
    ∑ a ∈ A, F (h * a) = ∑ a ∈ A', F (h * a) :=
  congrFun (GlobalTheory.HkB.dcOp_eq_and_level J ⊤ 1 x x' A A' F
    (fun k hk => ⟨k, hk, 1, J.one_mem, trivial, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun _ _ => rfl) (fun _ _ => trivial) (fun _ _ => trivial) hA hA' hx
    (fun k h => by simpa using hF k k.2 h)).1 h

theorem sum_inv_of_isDC {J : Subgroup G} {x : G} {A : Finset G} {F : G → ℂ} (hA : IsDC J x A)
    (hF : ∀ k ∈ J, ∀ h, F (h * k) = F h) (k : G) (hk : k ∈ J) (h : G) :
    ∑ a ∈ A, F (h * k * a) = ∑ a ∈ A, F (h * a) := by
  have := (GlobalTheory.HkB.dcOp_eq_and_level J ⊤ 1 x x A A F
    (fun k hk => ⟨k, hk, 1, J.one_mem, trivial, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun _ _ => rfl) (fun _ _ => trivial) (fun _ _ => trivial) hA hA ⟨1, 1, by simp⟩
    (fun k h => by simpa using hF k k.2 h)).2 ⟨k, hk⟩ h
  simpa [dcOp] using this

theorem mem_of_isDC {K L : Subgroup G} (hKL : K ≤ L) {x : G} (hx : x ∈ L) {A : Finset G} (hA : IsDC K x A) :
    ∀ a ∈ A, a ∈ L := by
  intro a ha
  obtain ⟨k₁, k₂, rfl⟩ := hA.1 a ha
  exact L.mul_mem (L.mul_mem (hKL k₁.2) hx) (hKL k₂.2)

structure Splits (J K L : Subgroup G) : Prop where
  le : K ≤ L
  mem : ∀ g ∈ L, g ∈ J ↔ g ∈ K
  dec : ∀ k ∈ J, ∃ k₁ ∈ K, ∃ k₂ ∈ J, k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l

theorem Splits.le' {J K L : Subgroup G} (hs : Splits J K L) : K ≤ J := fun g hg => (hs.mem g (hs.le hg)).2 hg

theorem Splits.isDC {J K L : Subgroup G} (hs : Splits J K L) {x : G} (hx : x ∈ L) {A : Finset G} (hA : IsDC K x A) :
    IsDC J x A := by
  have hAL := mem_of_isDC hs.le hx hA
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨k₁, k₂, rfl⟩ := hA.1 a ha
    exact ⟨⟨k₁, hs.le' k₁.2⟩, ⟨k₂, hs.le' k₂.2⟩, rfl⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a₁, ha₁, b₁, hb₁, e₁, c₁⟩ := hs.dec k₁ k₁.2
    obtain ⟨a, ⟨ha, hak⟩, -⟩ := hA.2 (a₁ * x) ⟨⟨a₁, ha₁⟩, 1, by simp⟩
    have hmem : a⁻¹ * (k₁ * x * k₂) ∈ J := by
      have : a⁻¹ * ((k₁ : G) * x * k₂) = a⁻¹ * (a₁ * x) * (b₁ * k₂) := by
        rw [e₁, mul_assoc a₁ b₁ x, (c₁ x hx).eq]; group
      rw [this]
      exact J.mul_mem (hs.le' hak) (J.mul_mem hb₁ k₂.2)
    refine ⟨a, ⟨ha, hmem⟩, ?_⟩
    rintro a' ⟨ha', hmem'⟩
    have h1 : a⁻¹ * a' ∈ J := by
      have : a⁻¹ * a' = (a⁻¹ * ((k₁ : G) * x * k₂)) * (a'⁻¹ * (k₁ * x * k₂))⁻¹ := by group
      rw [this]; exact J.mul_mem hmem (J.inv_mem hmem')
    have h2 : a⁻¹ * a' ∈ K := (hs.mem _ (L.mul_mem (L.inv_mem (hAL a ha)) (hAL a' ha'))).1 h1
    exact (hA.2 a' (hA.1 a' ha')).unique ⟨ha', by simp [K.one_mem]⟩ ⟨ha, h2⟩

theorem Splits.sum_transl {J K L : Subgroup G} (hs : Splits J K L) {x : G} (hx : x ∈ L) {A : Finset G}
    (hA : IsDC K x A) {F : G → ℂ} (hF : ∀ k ∈ K, ∀ h, F (h * k) = F h) {κ : G} (hκ : κ ∈ J) (h : G) :
    ∑ a ∈ A, F (h * κ * a) = ∑ a ∈ A, F (h * a * κ) := by
  have hAL := mem_of_isDC hs.le hx hA
  obtain ⟨a₁, ha₁, b₁, -, rfl, c₁⟩ := hs.dec κ hκ
  have e1 : a₁ * b₁ = b₁ * a₁ := (c₁ a₁ (hs.le ha₁)).eq.symm
  rw [e1, ← mul_assoc, sum_inv_of_isDC hA hF a₁ ha₁]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← mul_assoc, hF a₁ ha₁, mul_assoc, (c₁ a (hAL a ha)).eq, mul_assoc]

end Group

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

structure OffAt (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (K large₂ : Subgroup (GA D V)) : Prop where
  splits : Splits (levG V β L) K large₂
  chi : ∀ k ∈ K, levChi V β L k = 1

theorem inv_of_mem_mult {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {K large₂ : Subgroup (GA D V)} (hL : OffAt β L K large₂) {T : MMap M}
    (hT : T ∈ Mult θ M (levS V β L) (levChi V β L)) (v : M.Vec) : ∀ k ∈ K, ∀ h, T v (h * k) = T v h := by
  intro k hk h
  rw [((GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hT).lev v k (hL.splits.le' hk) h, hL.chi k hk, one_mul]

theorem heckeOn_mem_mult {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {K large₂ : Subgroup (GA D V)} (hL : OffAt β L K large₂) (hf : large₂ ≤ GfC V)
    {x : GA D V} (hx : x ∈ large₂) {A : Finset (GA D V)} (hA : IsDC K x A) {T : MMap M}
    (hT : T ∈ Mult θ M (levS V β L) (levChi V β L)) : heckeOn M A T ∈ Mult θ M (levS V β L) (levChi V β L) := by
  classical
  have hAL := mem_of_isDC hL.splits.le hx hA
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hT
  have h0 : IsMultMap θ M ∅ (levChi V β L) T := ⟨hT'.aut, hT'.cusp, fun _ _ hk => absurd hk (Set.notMem_empty _), hT'.equiv, hT'.cont⟩
  have hex : ∀ a : GA D V, ∃ T' : MMap M, a ∈ A → IsMultMap θ M ∅ (levChi V β L) T' ∧ ∀ v, T' v = rTr V a (T v) := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨T', h⟩ := _root_.GlobalTheory.isMultMap_rightTranslate_finite θ M ∅ (levChi V β L) a (hf (hAL a ha))
        (fun k hk => absurd hk (Set.notMem_empty _)) T h0
      exact ⟨T', fun _ => h⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose Ta hTa using hex
  have e : heckeOn M A T = ∑ a ∈ A, Ta a := by
    ext v g
    rw [MultilinearMap.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a ha => (congrFun ((hTa a ha).2 v) g).symm
  have h1 : IsMultMap θ M ∅ (levChi V β L) (heckeOn M A T) := by
    rw [← GlobalTheory.MultMem.mem_mult_iff, e]
    exact Submodule.sum_mem _ fun a ha => Submodule.subset_span (hTa a ha).1
  refine Submodule.subset_span ⟨h1.aut, h1.cusp, fun v k hk g => ?_, h1.equiv, h1.cont⟩
  show ∑ a ∈ A, T v (g * k * a) = levChi V β L k * ∑ a ∈ A, T v (g * a)
  rw [hL.splits.sum_transl hx hA (inv_of_mem_mult hL hT v) hk, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => hT'.lev v k hk _

theorem heckeLin_actL {β : GL (Fin V.rank) (Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {K large₂ : Subgroup (GA D V)}
    (hL : OffAt β (flagL L) K large₂) {x : GA D V} (hx : x ∈ large₂) {A : Finset (GA D V)} (hA : IsDC K x A)
    {F : GA D V → ℂ} (hF : ∀ k ∈ K, ∀ h, F (h * k) = F h) (g0 : Formalism.L2.DIV.G0 L.Pg L.r) :
    actL V β L g0 (heckeLin V A F) = heckeLin V A (actL V β L g0 F) := by
  funext h
  show actG0 V β L g0 (heckeLin V A F) h = ∑ a ∈ A, actG0 V β L g0 F (h * a)
  unfold actG0
  by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
  · simp only [dif_pos hk]
    have hκ : hk.choose ∈ levG V β (flagL L) := ⟨hk.choose_spec.1, hk.choose_spec.2.1, Subgroup.mem_top _⟩
    rw [heckeLin_apply, hL.splits.sum_transl hx hA hF hκ, Finset.mul_sum]
  · simp [dif_neg hk]

theorem offAt_of_place {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    (hβ : IsBaseFrame V β Λ N) {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}
    (hL : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P) {K large₂ : Subgroup (GA D V)}
    (hLg : ∀ g, g ∈ large₂ ↔ SuppAt e V g) (hK : ∀ g, g ∈ K ↔ g ∈ locPart V (KsphC V ∅) e) : OffAt β L K large₂ := by
  have hp : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨h1, h2, h3⟩ := (_root_.GlobalTheory.LevSplit.lev_split V β Λ N L hβ).2 P e _ hp hN hL
  obtain ⟨hf, hcf, -⟩ := (_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e _ hp
  have hc := ((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).1 _ hf hcf).2.2
  refine ⟨⟨fun g hg => (hLg g).2 ((hK g).1 hg).2, fun g hg => ?_, fun k hk => ?_⟩, fun k hk => ?_⟩
  · rw [h1 g ((hLg g).1 hg), hK]
    exact ⟨fun h => ⟨h, (hLg g).1 hg⟩, fun h => h.1⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, s₁, s₂, rfl⟩ := h3 k hk
    refine ⟨k₁, (hK _).2 ⟨(h1 _ s₁).1 hk₁, s₁⟩, k₂, hk₂, rfl, fun l hl => ?_⟩
    exact (hc (1 - (e + cA D e)) l k₂ (by rw [mul_sub, mul_one, hf, sub_self]) ((hLg l).1 hl) s₂).symm
  · have := (hK k).1 hk
    exact h2 k ((h1 k this.2).2 this.1) this.2

end GlobalTheory.HeckeModel
