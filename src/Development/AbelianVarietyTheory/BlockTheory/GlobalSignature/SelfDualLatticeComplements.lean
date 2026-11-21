import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.HermitianLattices.StatementLat

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeComplements

open NumberField Formalism.BasicNotions

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def perp (W : HSpace E) (x : W.V) : Submodule E W.V := LinearMap.ker (W.hT x)

theorem mem_perp (W : HSpace E) (x y : W.V) : y ∈ perp W x ↔ W.hD y x = 0 := Iff.rfl

def IsSelfDualLattice (W : HSpace E) (L : Submodule (𝓞 E) W.V) : Prop :=
  Submodule.IsLattice E L ∧ Formalism.HermitianLatticesTheory.dual W.hT L = L

def OfKind (W : HSpace E) (M P Q : ℕ) : Prop :=
  W.SigOK ∧ W.rank = M ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def Step (β : E) (P Q P' Q' : ℕ) : Prop :=
  (β = 1 ∧ 1 ≤ P ∧ P' = P - 1 ∧ Q' = Q) ∨ (β = -1 ∧ 1 ≤ Q ∧ P' = P ∧ Q' = Q - 1)

def HasComplement (W : HSpace E) (x : W.V) (M' P' Q' : ℕ) : Prop :=
  ∃ (L : Submodule (𝓞 E) W.V) (W' : HSpace E) (ι : W'.V →ₗ[E] W.V),
    IsSelfDualLattice W L ∧ x ∈ L ∧
    OfKind W' M' P' Q' ∧
    HSpace.IsIsomEmb W' W ι ∧
    LinearMap.range ι = perp W x ∧
    W'.L0.map (ι.restrictScalars (𝓞 E)) = L ⊓ (perp W x).restrictScalars (𝓞 E) ∧
    L = Submodule.span (𝓞 E) {x} ⊔ (L ⊓ (perp W x).restrictScalars (𝓞 E))

def ExistsPerpOver (E : Type) [Field E] [NumberField E] [StarRing E] : Prop :=
  ∀ (W : HSpace E) (M P Q : ℕ), OfKind W M P Q → 3 ≤ M →
    ∀ (β : E) (P' Q' : ℕ), Step β P Q P' Q' →
      ∃ x : W.V, W.hD x x = β ∧ HasComplement W x (M - 1) P' Q'

theorem injective_of_isIsomEmb {W' W : HSpace E} {ι : W'.V →ₗ[E] W.V}
    (h : HSpace.IsIsomEmb W' W ι) : Function.Injective ι := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  refine W'.nondeg.1 y fun z => ?_
  rw [← h y z, hy]
  simp

end General

def UnitVectorPerp (D : D7) : Prop :=
  @ExistsPerpOver D.host.E _ _ D.host.cmStar

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeComplements

end
