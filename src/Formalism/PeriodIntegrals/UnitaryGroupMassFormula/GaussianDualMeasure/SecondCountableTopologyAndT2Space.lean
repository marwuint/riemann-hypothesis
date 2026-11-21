import Mathlib

open ValuativeRel MeasureTheory

noncomputable section

namespace PI.GI

section Top

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem secondCountableTopology_and_t2Space : SecondCountableTopology F ∧ T2Space F :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  letI : (Valued.v (R := F)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := F).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  ⟨inferInstance, inferInstance⟩

instance secondCountable : SecondCountableTopology F := (secondCountableTopology_and_t2Space F).1

instance t2Space : T2Space F := (secondCountableTopology_and_t2Space F).2

end Top

end PI.GI
