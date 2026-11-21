import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FrobOrderSpec
import Formalism.LocalToGlobal.GroupLattices.TiedRec
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieIwLevTieOf
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CmpHyp0P
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.SelfDualAtColLevel
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.GTiedFOfIsRecCEv
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecThm

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.Mem.LocalPack

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

section Ext

variable {Os Ks O Kf O' Kf' : Type} [CommRing Os] [Field Ks] [Algebra Os Ks] [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field Kf']
  [Algebra O' Kf']

theorem extMap_φ (X : ExtOf Os Ks O Kf) (eO : O ≃+* O') (eK : Kf ≃+* Kf')
    (hc : ∀ x, eK (algebraMap O Kf x) = algebraMap O' Kf' (eO x)) (hfrac : IsFractionRing O' Kf')
    (hcomp : IsAdicComplete (IsLocalRing.maximalIdeal O') O') (x : Os) :
    (X.map eO eK hc hfrac hcomp).φ x = eO (X.φ x) := rfl

theorem extMap_φK (X : ExtOf Os Ks O Kf) (eO : O ≃+* O') (eK : Kf ≃+* Kf')
    (hc : ∀ x, eK (algebraMap O Kf x) = algebraMap O' Kf' (eO x)) (hfrac : IsFractionRing O' Kf')
    (hcomp : IsAdicComplete (IsLocalRing.maximalIdeal O') O') (y : Ks) :
    (X.map eO eK hc hfrac hcomp).φK y = eK (X.φK y) := rfl

end Ext

section Bridge

theorem frobOrder_eq (D : D7) (p : ℕ) : frobOrder D p = nFr D p := rfl

theorem pack_eq (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
    (h5 : 5 ≤ D.what₂.places.resChar w) (h2 : 2 ≤ nFr D (D.what₂.places.resChar w))
    (he : Even (nFr D (D.what₂.places.resChar w)))
    (I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : Formalism.L2.Herm.awayFrom₂ Lc (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ) :
    pack D u Lc w h5 h2 he I ψ = locPackC D u Lc w h5 h2 he I ψ := by
  first
    | with_reducible rfl
    | (delta pack locPackC frobOrder nFr; with_reducible rfl)

end Bridge

section Record

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

theorem recordAllTies_forms (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B) (hB) (CH) (hH) :
    (groupCompatibilityOfRecursion D sc Ce Lc I ψ hd H0 hL T B hBs hB CH hH).forms = T := rfl

end Record

end GlobalTheory.Mem.LocalPack
