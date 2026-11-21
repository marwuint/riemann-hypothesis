import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCommonModOfIsDiag

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.LocM.MapComp
open GlobalTheory.LocM.CommonMod

namespace GlobalTheory.LocM.StepMono

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem map_entry {R S T : Type} [CommRing R] [CommRing S] [CommRing T] {n : ℕ} (ψ : R →+* S) (φ : S →+* T)
    (a : GL (Fin n) R) (j l : Fin n) : φ (Matrix.GeneralLinearGroup.map ψ a j l) = φ.comp ψ (a j l) := rfl

end GlobalTheory.LocM.StepMono
