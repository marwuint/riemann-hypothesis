import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.Columns.AtTLemmas

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Abs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure Nbr (S : GSD K) where
  up : S.D → Finset S.D
  dn : S.D → Finset S.D
  mem_iff : ∀ d d' : S.D, d' ∈ up d ↔ d ∈ dn d'
  equiv : ∀ (g : S.G) (d d' : S.D), g • d' ∈ up (g • d) ↔ d' ∈ up d

variable {S : GSD K}

end Abs

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

variable {u : Pr.Word}

variable (R u) in

abbrev TopPt : Type := RowPt Pr R sel mu × DecoSet X.E (R.N R.m) (Pr.vT u) (rowSG Pr sel mu)

end Chain

section OrdDet

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def OrdDetFin : Prop :=
  ∀ N : Submodule (𝓞 E) (Sp E n), IsSdLat N → {Q : HeightOneSpectrum (𝓞 E) | ordDet Q N ≠ 0}.Finite

end OrdDet

end Formalism.L2.Ker
