import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Formalism.LocalToGlobal.Divisibility.RowSideTie

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftForms

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem jMt_injective (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  have hli := (D.what₂.jMt_basis μ j (Module.Free.chooseBasis _ _)).1
  have := hli.finite
  have := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))
  exact inj_of_li D.what₂.embLL (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _) hli

theorem carrier_subset (μ : D.what₂.Tup) (j : ℕ) : ∀ m ∈ (D.what₂.MtLat μ j).carrier, m ∈ Set.range (D.what₂.jMt μ j) := by
  rintro _ ⟨c, rfl⟩
  refine Finset.sum_induction _ (fun m => m ∈ Set.range (D.what₂.jMt μ j)) ?_ ⟨0, map_zero _⟩ fun v hv => ?_
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  · obtain ⟨x, rfl⟩ := D.what₂.MtLat_sub μ j v hv
    exact ⟨D.what₂.OtoLL (c (D.what₂.jMt μ j x)) • x, map_smulₛₗ _ _ _⟩

variable {R : RealDat D A Ks} {F : Face D A}

end Main

end GlobalTheory.Mem.LiftForms

end
