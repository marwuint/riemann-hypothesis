import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.QPl.EpsSupp

theorem exists_prod_of_mem_support_conv {G : Type} [Monoid G] : ∀ (n : ℕ) (f : Fin n → (G →₀ ℂ)) (g : G),
    g ∈ (conv (List.ofFn f)).support → ∃ x : Fin n → G, (∀ i, x i ∈ (f i).support) ∧ g = (List.ofFn x).prod := by
  classical
  intro n
  induction n with
  | zero =>
    intro f g hg
    simp only [List.ofFn_zero, conv, List.foldr_nil] at hg
    have := Finsupp.support_single_subset hg
    rw [Finset.mem_singleton] at this
    exact ⟨Fin.elim0, fun i => i.elim0, by simp [this]⟩
  | succ n ih =>
    intro f g hg
    rw [List.ofFn_succ] at hg
    simp only [conv, List.foldr_cons] at hg
    have h1 := Finsupp.support_sum hg
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g₀, hg₀, h2⟩ := h1
    have h3 := Finsupp.support_sum h2
    rw [Finset.mem_biUnion] at h3
    obtain ⟨g', hg', h4⟩ := h3
    have h5 := Finsupp.support_single_subset h4
    rw [Finset.mem_singleton] at h5
    obtain ⟨x, hx, hxe⟩ := ih (fun k => f k.succ) g' hg'
    refine ⟨Fin.cons g₀ x, fun i => Fin.cases hg₀ (fun k => hx k) i, ?_⟩
    rw [List.ofFn_succ, List.prod_cons, h5, hxe]
    simp

theorem eps_mem_grpAt {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} (F : QFam v t) (sc cT : ℕ → ℂ)
    (h0 : ∀ i β, (F.Q i).εL 0 β = Finsupp.single 1 1) (j : ℕ) (α : t.Ch j) :
    ∀ g ∈ ((F.pinTup sc cT).ε j α).support, g ∈ GlobalTheory.FinPl.grpAt (c.V j) (· ∈ (F.pinTup sc cT).Q) := by
  classical
  intro g hg
  dsimp only [QFam.pinTup] at hg ⊢
  split_ifs at hg with hc
  · have hg' := Finsupp.support_smul hg
    obtain ⟨x, hx, rfl⟩ := exists_prod_of_mem_support_conv _ _ g hg'
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    have hP : (F.Q i).q.v ∈ Finset.univ.image fun i => (F.Q i).q.v := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rcases hc with ⟨ρ, hρ⟩ | hj
    · obtain ⟨e, -, he⟩ := (F.Q i).εL_at j ρ hρ (2 * ρ) (by have := (F.Q i).hs; omega) (F.eqv j α i)
      have hxi := hx i
      rw [he] at hxi
      obtain ⟨a, -, hax⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hxi)
      rw [← hax]
      exact GlobalTheory.SuppGrp.mem_grpAt_of_suppAt D _ (F.Q i).q _ _ ((F.Q i).gl_loc _ _ _ a).1 _ hP
    · subst hj
      have hxi := hx i
      rw [h0] at hxi
      have h1 := Finsupp.support_single_subset hxi
      rw [Finset.mem_singleton] at h1
      rw [h1]
      exact one_mem _
  · simp at hg

end GlobalTheory.QPl.EpsSupp

