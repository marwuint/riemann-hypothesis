import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition

namespace GlobalTheory.ParHecke.Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

theorem exists_reps {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G)
    (ho : IsOpen (J : Set G)) (hc : IsCompact (J : Set G)) (g : G) :
    ∃ R : Finset G, (∀ j ∈ R, j ∈ J) ∧ ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J := by
  classical
  haveI : DiscreteTopology (G ⧸ J) := QuotientGroup.discreteTopology ho
  let f : G → G ⧸ J := fun j => QuotientGroup.mk (j * g)
  have hf : Continuous f := QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  have hfin : (f '' J).Finite := (hc.image hf).finite_of_discrete
  have hex : ∀ c ∈ f '' J, ∃ j ∈ J, f j = c := fun c hc => hc
  choose! s hs hs' using hex
  refine ⟨hfin.toFinset.image s, ?_, fun j hj => ⟨s (f j), ⟨?_, ?_⟩, ?_⟩⟩
  · intro j hj
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hj
    exact hs c (hfin.mem_toFinset.1 hc)
  · exact Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 ⟨j, hj, rfl⟩)
  · exact QuotientGroup.eq.1 (hs' (f j) ⟨j, hj, rfl⟩)
  · rintro y ⟨hy, hy'⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hy
    have : f (s c) = f j := QuotientGroup.eq.2 hy'
    rw [← this, hs' c (hfin.mem_toFinset.1 hc)]

theorem isOpen_parahoric : IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  have : (parahoric k A D : Set (GL (A ⊕ D) k)) = (KO k (A ⊕ D) : Set _) ∩
      ⋂ i, ⋂ j, (fun g : GL (A ⊕ D) k => g.1 (.inr i) (.inl j)) ⁻¹' {x : k | valuation k x < 1} := by
    ext g; simp [mem_parahoric]
  rw [this]
  refine SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  refine IsOpen.preimage (Units.continuous_val.matrix_elem _ _) ?_
  simpa [Valuation.restrict_lt_one_iff] using (valuation k).isOpen_ball 1

theorem isCompact_parahoric : IsCompact (parahoric k A D : Set (GL (A ⊕ D) k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ isOpen_parahoric)
    fun _ h => (mem_parahoric.1 h).1

theorem det_lower_ne {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) : j.1.toBlocks₂₂.det ≠ 0 := by
  obtain ⟨h, hh, rfl⟩ := hj
  intro h0
  have e1 : (GeneralLinearGroup.map (n := A ⊕ D) (algebraMap 𝒪[k] k) h).1.toBlocks₂₂ =
      (algebraMap 𝒪[k] k).mapMatrix h.1.toBlocks₂₂ := rfl
  rw [e1, ← RingHom.map_det] at h0
  have h1 : h.1.toBlocks₂₂.det = 0 := Subtype.ext h0
  set u := GeneralLinearGroup.map (n := A ⊕ D) (IsLocalRing.residue 𝒪[k]) h with hu
  have h21 : u.1.toBlocks₂₁ = 0 := by
    ext i j
    exact hh (i := .inr i) (j := .inl j) (show false < true by decide)
  have h22 : u.1.toBlocks₂₂.det = 0 := by
    have : u.1.toBlocks₂₂ = (IsLocalRing.residue 𝒪[k]).mapMatrix h.1.toBlocks₂₂ := rfl
    rw [this, ← RingHom.map_det, h1, map_zero]
  have := u.det_ne_zero
  rw [← fromBlocks_toBlocks u.1, h21, det_fromBlocks_zero₂₁, h22, mul_zero] at this
  exact this rfl

theorem exists_isReps (g : GL (A ⊕ D) k) : ∃ R d, IsReps g R d := by
  classical
  obtain ⟨R, h1, h2⟩ := exists_reps _ isOpen_parahoric isCompact_parahoric g
  refine ⟨R, fun j => if h : j.1.toBlocks₂₂.det ≠ 0 then Units.mk0 _ h else 1, fun j hj => ⟨h1 j hj, ?_⟩, h2⟩
  simp [det_lower_ne (h1 j hj)]

theorem exists_isRepsK (g : GL D k) : ∃ R, IsRepsK g R := by
  classical
  obtain ⟨R, h1, h2⟩ := exists_reps (KO k D) SplitFlip.isOpen_KO SplitFlip.isCompact_KO g
  refine ⟨R.image (· * g), ?_, fun κ hκ => ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨j, h1 j hj, 1, one_mem _, by simp⟩
  · obtain ⟨j, ⟨hj, hj'⟩, hu⟩ := h2 κ hκ
    refine ⟨j * g, ⟨Finset.mem_image_of_mem _ hj, hj'⟩, ?_⟩
    rintro y ⟨hy, hy'⟩
    obtain ⟨j2, hj2, rfl⟩ := Finset.mem_image.1 hy
    rw [hu j2 ⟨hj2, hy'⟩]

end GlobalTheory.ParHecke.Model

end
