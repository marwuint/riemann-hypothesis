import Formalism.SharpRestriction.CuspSpanNormBounds.RowsOneGenusOfCyclic

noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Formalism.HermitianLatticesTheory

section Conj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem unimodAt_of_unimod {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (L : Submodule (𝓞 E) V) (hlat : Submodule.IsLattice E L) (hu : IsUnimodular h L)
    (p : Ideal (𝓞 E)) : IsUnimodularAt h p L := by
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := FaithfulSMul.algebraMap_injective _ _
  have hst : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
    fun r => cyc_star_int r
  have hfg : L.FG := Submodule.IsLattice.fg (A := E) (self := hlat)
  unfold IsUnimodularAt
  rw [locDual_dualAt_loc h hinj hst]
  have e1 := locDual_loc_dual_le h p L
  have e2 := locDual_dualAt_le h hst p L hfg
  unfold IsUnimodular at hu
  rw [hu] at e1 e2
  exact le_antisymm e2 e1

theorem unimod_mem_genus (hU : LocUnimod) (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (L M : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) (hM : Submodule.IsLattice E M)
    (huL : IsUnimodular S.hT L) (huM : IsUnimodular S.hT M) : M ∈ genus S.hT L :=
  ⟨hM, fun p hp => hU F E hc S L M hL hM p hp (unimodAt_of_unimod S.hT L hL huL p) (unimodAt_of_unimod S.hT M hM huM p)⟩

theorem unimodular_mem_genus (hU : LocUnimod) (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (M : Submodule (𝓞 E) S.V) (hM : Submodule.IsLattice E M) (huM : IsUnimodular S.hT M) : M ∈ genus S.hT S.L0 :=
  unimod_mem_genus hU hc S S.L0 M S.standardTuple_isLattice hM S.baseLattice_isUnimodular huM

end Conj

end Formalism.MainNotions.BridgeRowsGenus

end
