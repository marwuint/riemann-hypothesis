import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc

namespace GlobalTheory.Unfold.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gmap_one (Λ : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) Λ = Λ := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_mul (a b : GV D) (Λ : LV D) : Formalism.HermitianLatticesTheory.gmap (a * b) Λ = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b Λ) := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem adapt_one {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : Adapt (1 : GV D) F F :=
  ⟨Subgroup.one_mem _, fun a => by simp⟩

theorem unitriangular_lattice_stabiliser_sub_frame_automorphisms {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (Λ : LV D) : NLam Λ F ⊆ Aut0 F Λ := by
  rintro n ⟨⟨h1, h2⟩, h3, h4⟩
  refine ⟨⟨h1, fun a => ?_⟩, h2⟩
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have hz : frame F (Fin.last _) ∈ orth (VS D) (Xsp F) := by
      simp only [orth, Submodule.mem_iInf, frame, FlagG.fvec, Fin.snoc_last, LinearMap.mem_ker]
      intro x hx
      refine Submodule.span_induction (p := fun x _ => (VS D).hT x F.fl.z = 0) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨a, rfl⟩; exact F.fl.z_orth a
      · simp
      · intro x y _ _ a b; simp [a, b]
      · intro c x _ a; simp [a]
    have := h4 _ hz
    have e : Xflag F (Fin.last D.R.rS).val = Xsp F := by
      simp only [Xflag, FlagG.Xa, Xsp, FlagG.X, Fin.val_last]
      congr 1; ext v; simp
    rwa [e]
  · apply h3
    apply Submodule.subset_span
    exact ⟨i, by simp, by simp [frame, FlagG.fvec]⟩

section
variable {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')

theorem mem_gmap (h : GV D) (Λ : LV D) (x) : x ∈ Formalism.HermitianLatticesTheory.gmap h Λ ↔ h.symm x ∈ Λ := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hx; exact ⟨_, hx, by simp⟩

theorem gmap_sup (h : GV D) (A B : LV D) : Formalism.HermitianLatticesTheory.gmap h (A ⊔ B) = Formalism.HermitianLatticesTheory.gmap h A ⊔ Formalism.HermitianLatticesTheory.gmap h B :=
  Submodule.map_sup _ _ _

variable {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}

theorem h_add_right (p : PlF D) (x y y' : Vp D p) : (locH Z p).h x (y + y') = (locH Z p).h x y + (locH Z p).h x y' := by
  show LocFacts₂ _ _ _ _ = LocFacts₂ _ _ _ _ + LocFacts₂ _ _ _ _
  simp only [LocFacts₂, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]

theorem h_smul_right (p : PlF D) (c) (x y : Vp D p) : (locH Z p).h x (c • y) = (Z.M p).L.cj c * (locH Z p).h x y := by
  show LocFacts₂ _ _ _ _ = _ * LocFacts₂ _ _ _ _
  simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ext_unitary {p : PlF D} {h : GV D} (hh : h ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {g} (hg : Ext p h g) :
    LocNG.IsUnitary (locH Z p) g := by
  have key : ∀ a b, (locH Z p).h (g (baseChange₂ D p a)) (g (baseChange₂ D p b)) = (locH Z p).h (baseChange₂ D p a) (baseChange₂ D p b) := by
    intro a b
    rw [hg, hg]
    show LocFacts₂ _ _ _ _ = LocFacts₂ _ _ _ _
    rw [baseChangeAt_form _ _ (Z.hcj p), baseChangeAt_form _ _ (Z.hcj p)]
    simp only [brS]; rw [hh]
  have z1 : ∀ y, (locH Z p).h 0 y = 0 := fun y => by
    have := (locH Z p).h_smul_left 0 0 y; simpa using this
  have z2 : ∀ x, (locH Z p).h x 0 = 0 := fun x => by
    have := h_smul_right (Z := Z) p 0 x 0; simpa using this
  intro x y
  have hx : x ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := by rw [span_baseChange_eq_top]; trivial
  have hy : y ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := by rw [span_baseChange_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | zero => rw [map_zero, z1, z1]
  | add a b _ _ ha hb => rw [map_add, (locH Z p).h_add_left, (locH Z p).h_add_left, ha, hb]
  | smul c a _ ha => rw [map_smul, (locH Z p).h_smul_left, (locH Z p).h_smul_left, ha]
  | mem a ha =>
    obtain ⟨a, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | zero => rw [map_zero, z2, z2]
    | add a b _ _ ha hb => rw [map_add, h_add_right, h_add_right, ha, hb]
    | smul c a _ ha => rw [map_smul, h_smul_right, h_smul_right, ha]
    | mem b hb => obtain ⟨b, rfl⟩ := hb; exact key a b

end

end GlobalTheory.Unfold.Model
