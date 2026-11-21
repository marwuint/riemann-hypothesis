import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetFixedVectorLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionFixedSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictlyDominantHeckeKernel

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem c3 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C3 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hJf hpos V _ _ π hπ
  exact ⟨_root_.GlobalTheory.CompanionTheory.Casselman.mk_mem_fixed_jac k N h d hd J hJo hJc hJf hpos V π hπ.1,
    _root_.GlobalTheory.CompanionTheory.JacquetLemma.jacquet_surjective k N h d hd J hJo hJc hJf hpos V π hπ,
    _root_.GlobalTheory.CompanionTheory.Lbc.heckeOp_nilpotent_on_ker k N h d hd J hJo hJc hJf hpos V π hπ.1⟩

end GlobalTheory.CompanionTheory.Lbc
