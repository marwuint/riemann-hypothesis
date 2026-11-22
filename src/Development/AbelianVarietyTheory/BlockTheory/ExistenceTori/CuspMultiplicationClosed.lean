import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodUniformizationCusps

open NumberField Formalism.L2.Pj Formalism.L2.PjFree ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def Cusp (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (_hn : Even n) :
    Submodule c.F (Rul Xo c) where
  carrier := {f | f ∈ sec Xo c a n ∧
    ∀ σ : c.F →+* ℂ, GoodEmb c σ → ∀ k : (U σ).Comp, rdU (U σ) f k ∈ ((U σ).X k).SS (laU (U σ) a n k)}
  zero_mem' := ⟨Submodule.zero_mem _, fun σ _ k => by
    rw [map_zero]
    exact (siegelSpaceAlgebra_holds r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1.1⟩
  add_mem' := fun {f g} hf hg => ⟨Submodule.add_mem _ hf.1 hg.1, fun σ hσ k => by
    rw [map_add]
    exact (siegelSpaceAlgebra_holds r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1.2.1 _ (hf.2 σ hσ k) _ (hg.2 σ hσ k)⟩
  smul_mem' := fun b f hf => ⟨Submodule.smul_mem _ b hf.1, fun σ hσ k => by
    rw [map_smulₛₗ]
    exact (siegelSpaceAlgebra_holds r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1.2.2 _ _ (hf.2 σ hσ k)⟩

theorem mem_cusp (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n)
    (f : Rul Xo c) : f ∈ Cusp U a n hn ↔ f ∈ sec Xo c a n ∧
      ∀ σ : c.F →+* ℂ, GoodEmb c σ → IsHolCusp (U σ).X (laU (U σ) a n) (rdU (U σ) f) := Iff.rfl

end GlobalTheory.IndefiniteRowSideFullHecke.GoodUniformizationCusps
