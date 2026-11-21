import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapTheorem
import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.RowChiReal
import Formalism.WachLatticeTwists.SplitClassesAll.Statement
import Formalism.WachLatticeTwists.SplitLocalLifts.Cocycles1MapOfEquivariant
import Formalism.WachLatticeTwists.SplitLocalLifts.SplitLocalLiftProofs.NatCastPowSmul
import Formalism.WachLatticeTwists.SplitLocalLifts.SplitLocalLiftProofs.LocLift
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.LocDualOrth
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.QuotLen
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ExistsBasisOfLattice
import Formalism.WachLatticeTwists.CharacterSplitJumps.WachTwistTheoremFromTorsionBound
import Formalism.WachLatticeTwists.CoprimeLiftBounds.StatBridgeChiOne
import Formalism.WachLatticeTwists.Statement
import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.MemAnnih
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MinimalExponentAttained
import Formalism.WachLatticeTwists.HodgeTateChains.XiAdicFiltrationData
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Imports
import Formalism.WachLatticeTwists.HodgeTateChains.Statement
import Formalism.WachLatticeTwists.TorsionLengthCounts.SubmoduleLengthBoundStatement
import Formalism.WachLatticeTwists.HodgeTateChains.H2KilledByTateDuality
import Formalism.WachLatticeTwists.HodgeTateChains.GammaIterateMatrixCongruence
import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.FirstSummandActionMem
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveDeltaClause
import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.PropLocBK
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Bridge
import Formalism.CharacterColumnKernels.IdempotentNormalForms.CharacterColumnKernelsOfBlockChiCOfBlockChiOne
import Formalism.WachLatticeTwists.TorsionLengthCounts.RowCol
import Formalism.CharacterColumnKernels.CharacterColumnKernelEqualityForm
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
