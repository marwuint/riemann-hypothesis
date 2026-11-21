import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsKitWithKitWith
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionInvariantFrameFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier
open scoped ENNReal

namespace GlobalTheory.CovHt.Link

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

abbrev unf (s : FinalTheorems S κ) : ∀ σ : κ.c.F →+* ℂ, Formalism.L2.Pj.Unf s.Xo κ.c σ N := fun σ => GlobalTheory.ThetaDictCompare.toU (s.U σ)

def drSym (la : AllWt.Weight S.Dw) : Sym D.host.E →₀ ℤ :=
  ∑ z : Letter S.Dw, Finsupp.single (fun _ => false, none, .inl (z.1, z.2)) (-exOf S.Dw la 0 (some z))

variable {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)

def Over (Z : Comp s.Xo κ.c) : Prop := letI := (constF κ.e (Φ.C k).Y).toAlgebra; LiesOn Z (Φ.C k).y0

end GlobalTheory.CovHt.Link

end
