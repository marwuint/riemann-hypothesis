import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def EtaleTateTwistSectionsDeterminedByPointsOfProper : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ j : ℕ,
  ∀ {X : Scheme.{0}} (p : X ⟶ S k), IsProper p → ∀ s : Sec (tw (l ^ j) 0) X,
    ((∀ y : Pt p, Sec.res y.1 s = 0) → s = 0) ∧
    (ConnectedSpace X → ∀ y y' : Pt p, Sec.res y.1 s = Sec.res y'.1 s)

end LateralTheory.EtaleTrace
