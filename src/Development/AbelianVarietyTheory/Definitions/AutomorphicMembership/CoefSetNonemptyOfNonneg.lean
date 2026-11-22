import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonnegAdmissibleIffPositiveDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUniqueIsVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDiscreteValuationRingIntO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartExtensionHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameMoveHolds
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsUniqueH0Section
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcBasisBaseChange

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.ArcQ (Wit LieImg ArcBasis)
open GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints (EpsPt IsLetters)

namespace GlobalTheory.LocM.FJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

structure DVF (p : ℕ) : Type where

  C : SCF p

  K : Subfield ↥C.S

  closed : IsClosed (K : Set ↥C.S)

  dvr : IsDiscreteValuationRing ↥(intO ↥K)

namespace DVF

variable {p : ℕ} (F : DVF p)

abbrev O : Type := ↥(intO ↥F.K)

instance : IsDiscreteValuationRing F.O := F.dvr

end DVF

section Cusp

variable {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {A : Type} [CommRing A] [IsDomain A]

@[reducible] def withForm {b : O →+* A} (a : ArcIn Dw l β A b) (γ : levelForms H l.M' a.D₀.X)
    (h : γ ∈ admitted H l.M' a.D₀.X) : ArcIn Dw l β A b :=
  { a with be := γ.1, be_symm := γ.2.1, be_pos := h.1, be_adj := γ.2.2.1, be_dvd := h.2 }

variable (Dw l β A) in

structure Cusp : Type 1 where

  b : O →+* A

  a : ArcIn Dw l β A b

  e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → EpsPt a.D₀

  letters : ∃ io : c.F →+* FractionRing A, IsLetters a io e

namespace Cusp

variable (t : Cusp Dw l β A)

abbrev Forms : Type := levelForms H l.M' t.a.D₀.X

end Cusp

variable {p : ℕ} {W : ValuationSubring ℂ} {F : DVF p}

end Cusp

section Arcs

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

abbrev CuspOn (Z : Mdl Y i₀) (F : DVF p) : Type 1 := Cusp Dw Z.i.l (Z.i.c.V W).subtype F.O

variable {Z : Mdl Y i₀} {F : DVF p} (t : CuspOn Z F)

variable {e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ} {M : Z.X.Modules} (T : GrTriv Z e M) (f : Γ(M, Z.genO))

end Arcs

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p)

end GlobalTheory.LocM.FJ

namespace GlobalTheory.LocM

namespace FJ

end FJ

end GlobalTheory.LocM
