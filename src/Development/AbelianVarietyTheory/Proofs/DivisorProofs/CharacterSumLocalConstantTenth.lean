import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeterminingLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogClassNumberAtLe
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ChainClassNumbers

theorem card_orbits_le_principal {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {G' D' : Type} [Group G'] [MulAction G' D']
    (p : D' → DecoSet E n ST SG) (hp : Function.Injective p)
    (h : ∀ (g : UF E n) (x : D'), ∃ g' : G', p (g' • x) = (g, (1 : GLG E n SG)) • p x)
    [Finite (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF E n)).prod (⊥ : Subgroup (GLG E n SG))) (DecoSet E n ST SG))] :
    Nat.card (MulAction.orbitRel.Quotient G' D') ≤
      Nat.card (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF E n)).prod (⊥ : Subgroup (GLG E n SG))) (DecoSet E n ST SG)) := by
  refine Nat.card_le_card_of_injective
    (fun c : MulAction.orbitRel.Quotient G' D' =>
      (Quotient.mk (MulAction.orbitRel _ _) (p (Quotient.out c)) :
        MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF E n)).prod (⊥ : Subgroup (GLG E n SG))) (DecoSet E n ST SG))) ?_
  intro c c' hcc
  obtain ⟨⟨⟨g, k⟩, hgk⟩, hg⟩ := Quotient.exact hcc
  have hk : k = 1 := (Subgroup.mem_prod.1 hgk).2
  subst hk
  obtain ⟨g', hg'⟩ := h g (Quotient.out c')
  have he : g' • Quotient.out c' = Quotient.out c := hp (hg'.trans hg)
  rw [← Quotient.out_eq c, ← Quotient.out_eq c']
  exact Quotient.sound ⟨g', he⟩

end GlobalTheory.ChainClassNumbers
