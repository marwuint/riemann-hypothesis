import Mathlib
import Formalism.LocalToGlobal.Columns.AtTLemmas

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

abbrev KerArg (u : Pr.Word) : Type := ∀ j : ℕ, ColV W Ch u j →ₗ[X.K] ColV W Ch u (j + 1)

variable {W Ch}

def KernelArgumentHypothesisScalar {u : Pr.Word} (kk : KerArg W Ch u) (c : ℕ → {P // P ∈ Pr.vT u} → X.Kˣ) : Prop :=
  ∀ j, j < R.m → ∀ P, (UOp W Ch u (j + 1) P).comp (kk j) = ((c j P : X.Kˣ) : X.K) • (kk j).comp (UOp W Ch u j P)

def cProdC (W : Wts X Pr.Word R) {u : Pr.Word} (c : ℕ → {P // P ∈ Pr.vT u} → X.Kˣ) (w : HeightOneSpectrum (𝓞 X.K)) (j : ℕ) : X.Kˣ :=
  ∏ P ∈ VVTc W u w, c j P

end Col

end Formalism.L2.Col
