import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NormDetAtConstOfPlacewise

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam.Pad

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (Φ : s.Flag)
  {C : CxSt D.what₂.LL} (hm : ∀ k, Mets (Φ.C k) C)
  (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ))
  (hj : ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) (hA : AdmEx S κ) {ng : NgPkg}

def padTrue (L : LocSt D N j ng) (G : GlobSt fun p => (L.loc p).Mdl) : PadPkg D N j s.Comp jC ng :=
  padAt s L G (admissible_representation_factorisation S κ jC hj hA) (flatSt s Φ hm) (arIn s Φ hm)

variable (L : LocSt D N j ng) (G : GlobSt fun p => (L.loc p).Mdl)

theorem padTrue_arDeg : (padTrue s Φ hm jC hj hA L G).arDeg = (arIn s Φ hm).arDeg := rfl

end GlobalTheory.ShFam.Pad
