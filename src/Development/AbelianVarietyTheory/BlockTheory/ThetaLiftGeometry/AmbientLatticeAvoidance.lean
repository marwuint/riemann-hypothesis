import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AmbientLatticeAvoidance

section Concrete

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

abbrev rkTop (R : Ranks) : ℕ := (R.N R.m - 1) + 0

open Classical in

def lamTop (sharp : Bool) (P : HeightOneSpectrum (𝓞 X.E)) (h : HomE X.E (rkTop R) (rkTop R)) : X.K :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.lamGBS (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t R.m (R.N R.m - 1) 0 h
      else LocE.lamGB (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t R.m (R.N R.m - 1) 0 h)
  else LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P) R.r (R.N R.m - 1) h

abbrev Pt (u : Pr.Word) (i : ℕ) : Type := ChPt (R := R) sel mu u i × Option (L.β i) × Set (Sp X.E (R.N i))

variable (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop R))) (dep : HeightOneSpectrum (𝓞 X.E) → ℕ)

end Concrete

end GlobalTheory.IndefiniteRowSideFullHecke.AmbientLatticeAvoidance
