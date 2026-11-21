import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCover

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverNorm

section Induces

open GlobalTheory.Cartier GlobalTheory.CxPts ReciprocityTheory.ChartRestriction.G

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

theorem generatesAt_genAt_pow (D : Y.Dv) (k : ℕ) (x : Y.X) : (k • D).GeneratesAt x (genAt D x ^ k) := by
  have := CartierDiv.isEqn_iff_generatesAt_inv.1 ((Base.isEqn_eqn D x).nsmul k)
  rwa [Units.val_pow_eq_pow_val, ← inv_pow, ← Units.val_inv_eq_inv_val] at this

end Induces

end GlobalTheory.CoverNorm
