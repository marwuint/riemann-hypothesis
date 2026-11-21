import Development.WeilBound.CoreStatements.PadicHodgeComparison.KatzMessingTheorem.KatzMessingT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison

namespace CompanionTheory.KM.Cris

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [Fintype k] [CharP k p]

abbrev DX {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) : Type 1 :=
  Wc.D p (B.schFn q) (RingHom.id k) n

abbrev Dcr (Y : Var k) (n : ℕ) : Type 1 := DX p Y.s n

variable {p}

variable (p)

variable (k)

variable {k}

variable (k)

class FinDim : Prop where
  fin : ∀ (Y : Var k) (n : ℕ), FiniteDimensional (Wc.K₀ p k) (Dcr p Y n)

variable {k}

instance [h : FinDim p k] (Y : Var k) (n : ℕ) : FiniteDimensional (Wc.K₀ p k) (Dcr p Y n) := h.fin Y n

instance [FinDim p k] (Y : Var k) (n : ℕ) : Small.{0} (Dcr p Y n) := Module.Finite.small.{0} (Wc.K₀ p k) _

end CompanionTheory.KM.Cris
