import Formalism.GradedWeylDivisibility.StatementA
import Formalism.RankGapBounds.CloudMinFalse
import Formalism.RankGapBounds.TheoremALocOfLemmaA
import Formalism.PieriBlockIdeals.Statement
import Formalism.PieriBlockIdeals.StatementJ

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LA

open Formalism.GradedWeylDivisibility

def lamU (r n : ℕ) (ν : Fin n → ℕ) : Fin r → ℤ :=
  fun a => (rowNu (r := r) ν a : ℤ) + ((r : ℤ) - 1 - (a.val : ℤ))

def InclZ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (l e : ℕ) : Prop :=
  ∃ m : ℕ, ¬ l ∣ m ∧ ∀ x ∈ dualWeyl ℤ r n ν, ((m * l ^ e : ℕ) : ℤ) • x ∈ weyl ℤ r n hn ν

def exZ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (l : ℕ) : ℕ := sInf {e : ℕ | InclZ r n hn ν l e}

def ExZSpec : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ r n hn ν l (exZ r n hn ν l)

def ExactExponentRankTwo : Prop :=
  ∀ (n : ℕ) (ν : Fin n → ℕ) (l : ℕ),
    Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 n ν) l =
      Formalism.RankGapBounds.JumpSetsAlt.maxVal l (rowNu (r := 2) ν 0 - rowNu (r := 2) ν 1)

def LatticeInclusionTrivialWeight : Prop :=
  ∀ (r : ℕ) (hn : 0 ≤ r) (ν : Fin 0 → ℕ) (l : ℕ), l.Prime →
    InclZ r 0 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r 0 ν) l)

def LatticeInclusionRankOne : Prop :=
  ∀ (n : ℕ) (hn : n ≤ 1) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ 1 n hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 1 n ν) l)

def LemmaAZ_r2n1 : Prop :=
  ∀ (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) (l : ℕ), l.Prime →
    InclZ 2 1 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 1 ν) l)

def LemmaAZ_r2n2 : Prop :=
  ∀ (hn : 2 ≤ 2) (ν : Fin 2 → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ 2 2 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 2 ν) l)

def LatticeInclusionRankLeTwo : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r), r ≤ 2 → ∀ ν : Fin n → ℕ, Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ r n hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l)

def SharpInclusionRankTwoOneColumn : Prop :=
  ∀ (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) (l e : ℕ), l.Prime →
    (InclZ 2 1 hn ν l e ↔ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0) ≤ e)

def SharpInclusionRankTwoTwoColumns : Prop :=
  ∀ (hn : 2 ≤ 2) (ν : Fin 2 → ℕ), Antitone ν → ∀ l e : ℕ, l.Prime →
    (InclZ 2 2 hn ν l e ↔ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1) ≤ e)

end Formalism.CohomologicalDescent.LA
