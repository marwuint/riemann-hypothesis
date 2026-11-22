import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalWhittaker
import Development.AutomorphicSpectrum.Proofs.SemilocalMultiplicity.GelfandGraevMultOneHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMirabolicWhittakerEigenspace

noncomputable section

open Matrix

namespace PositivityTheory.Mirab.Restr

section Uni

variable {k : Type} [Field k] {d : ℕ}

abbrev upU (d : ℕ) (k : Type) [Field k] : Subgroup (GL (Fin d) k) := Formalism.L2.DIV.unip k d

theorem mem_upU {u : GL (Fin d) k} : u ∈ upU d k ↔
    (∀ i j : Fin d, j < i → (u : Matrix (Fin d) (Fin d) k) i j = 0) ∧ ∀ i, (u : Matrix (Fin d) (Fin d) k) i i = 1 :=
  Iff.rfl

def sdSum (M : Matrix (Fin d) (Fin d) k) : k := Formalism.L2.SG.GGMirabolic.superdiag d M

end Uni

section Wh

open ReciprocityTheory.Ty.Fin

variable {k : Type} [Field k] [Fintype k] [DecidableEq k] {d : ℕ}

def sdg (u : GL (Fin d) k) : k := sdSum (u : Matrix (Fin d) (Fin d) k)

end Wh

section Whit

open ReciprocityTheory.Ty.Fin Formalism.L2.SG.GGMirabolic

variable {k : Type} [Field k] [Fintype k] [DecidableEq k] {d : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem psiU_eq (ψ₀ : AddChar k ℂ) (u : GL (Fin d) k) : psiU ψ₀ u = ψ₀ (sdg u) := rfl

end Whit

end PositivityTheory.Mirab.Restr
