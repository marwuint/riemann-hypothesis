import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.BlowOpen

theorem exists_specializes_of_dense {X : Type} [TopologicalSpace X] [QuasiSober X] [NoetherianSpace X] (S : Set X)
    (hSo : IsOpen S) (hSd : Dense S) (x : X) : ∃ w ∈ S, w ⤳ x := by
  classical
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hCi : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent x) := isClosed_of_mem_irreducibleComponents _ hC
  have hη : IsGenericPoint hCi.genericPoint (irreducibleComponent x) := by
    simpa [hCc.closure_eq] using hCi.isGenericPoint_genericPoint_closure
  let F := ⋃ C' ∈ (irreducibleComponents X \ {irreducibleComponent x}), C'
  have hFc : IsClosed F := (NoetherianSpace.finite_irreducibleComponents.diff).isClosed_biUnion
    (fun C' h => isClosed_of_mem_irreducibleComponents C' h.1)
  have hηF : hCi.genericPoint ∉ F := by
    simp only [F, Set.mem_iUnion]
    rintro ⟨C', ⟨hC', hne⟩, hηC'⟩
    have hsub : irreducibleComponent x ⊆ C' := fun y hy =>
      (hη.specializes hy).mem_closed (isClosed_of_mem_irreducibleComponents C' hC') hηC'
    exact hne (Set.mem_singleton_iff.2 (hC.eq_of_le hC'.1 hsub).symm)
  obtain ⟨w, hwF, hwS⟩ := hSd.inter_open_nonempty Fᶜ hFc.isOpen_compl ⟨_, hηF⟩
  have hwC : w ∈ irreducibleComponent x := by
    by_contra h
    apply hwF
    simp only [F, Set.mem_iUnion]
    refine ⟨irreducibleComponent w, ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => h ?_⟩,
      mem_irreducibleComponent⟩
    rw [← Set.mem_singleton_iff.1 e]; exact mem_irreducibleComponent
  exact ⟨_, (hη.specializes hwC).mem_open hSo hwS, hη.specializes mem_irreducibleComponent⟩

theorem exists_specializes_of_dense_scheme (N : Scheme.{0}) [IsLocallyNoetherian N] (W : Set N) (hWo : IsOpen W)
    (hWd : Dense W) (n : N) : ∃ w ∈ W, w ⤳ n := by
  obtain ⟨_, ⟨O, hO, rfl⟩, hnO, -⟩ := N.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ n) isOpen_univ
  haveI : IsNoetherianRing Γ(N, O) := IsLocallyNoetherian.component_noetherian ⟨O, hO⟩
  obtain ⟨w, hw, hwn⟩ := @exists_specializes_of_dense (O : Set N) _ O.isOpen.isOpenEmbedding_subtypeVal.quasiSober
    (noetherianSpace_of_isAffineOpen O hO) (Subtype.val ⁻¹' W : Set (O : Set N)) (hWo.preimage continuous_subtype_val)
    (hWd.preimage O.isOpen.isOpenMap_subtype_val) ⟨n, hnO⟩
  exact ⟨w, hw, hwn.map continuous_subtype_val⟩

end GlobalTheory.BlowOpen
