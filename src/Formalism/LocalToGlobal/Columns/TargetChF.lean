import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.ColFormsLemmas

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem chfok_false (hQ : Q = ∅) (P : Q) : False := by
  obtain ⟨p, hp⟩ := P
  simp [hQ] at hp

def chfokLift (hQ : Q = ∅) (d : DecoSet X.E n ST SG) : DecoF X.E n ST SG Q :=
  ⟨(d, fun _ => 1), fun P _ => (chfok_false hQ P).elim⟩

end Gen

end Formalism.L2.Col
