import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapTheorem
import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.RowChiReal
import Formalism.WachLatticeTwists.SplitLocalLifts.SplitLocalLiftProofs.NatCastPowSmul
import Formalism.WachLatticeTwists.SplitLocalLifts.SplitLocalLiftProofs.LocLift
import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.PropLocBK
import Formalism.WachLatticeTwists.TorsionLengthCounts.LengthHomCoker

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG IsCycOn)

theorem blk_ko {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type} {d : Type}
    [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))} {α : Type}
    [DecidableEq α] (bl : d → α)
    (ρk : ∀ k : α, R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O) (k : α)
    (h : Fintype.card {a // bl a = k} = 1) : Nonempty (blockRestrictedRepresentationType bl ρk k ≃ₗ[O] KO O) := by
  obtain ⟨hu⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 h
  exact ⟨(LinearEquiv.funUnique {a // bl a = k} O (KO O) : ({a // bl a = k} → KO O) ≃ₗ[O] KO O)⟩

end Formalism.RepresentationBoundsCohomology.FIN
