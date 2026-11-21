import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.CoboundaryTransfers.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def CmpIso (W : LocWach PD LL O v n) (l : ℕ) (T : LocLat G Qp LL O) : Prop :=
  (∀ x : ↥(W.N T), W.cmp T x = 0 ↔ ∃ y : ↥(W.N T), x = (letπ : LetA O n) • y) ∧
  Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T x) = Dcris PD T.ρ ∧
  (∀ i : ZMod n, Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T ((letE i : LetA O n) • x))
      = DcrisL PD T.ρ (W.emb i)) ∧
  (∀ (x : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T),
    W.cmp T ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ =
      (l : LL) ^ m • φVB PD (LL := LL) (V := T.V) (W.cmp T x))

end Generic

end GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison
