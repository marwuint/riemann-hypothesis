import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR

variable {k : Type} [CommRing k] {X X' : Scheme.{0}}

def affIncl (X : Scheme.{0}) : X.affineOpens ⥤ X.Opens :=
  Monotone.functor (f := fun U : X.affineOpens ↦ U.1) fun _ _ h ↦ h

def affSec (s : X ⟶ Sp k) (q : ℕ) : AffOp X ⥤ ModuleCat.{0} k :=
  letI := algΓ s
  (affIncl X).op ⋙ sectionsPresheaf k (Omega s q)

theorem algebraMap_sec_eq (s : X ⟶ Sp k) (U : X.Opens) (r : k) :
    letI := algΓ s
    algebraMap k (Sec s U) r = restrictGlobal X U (algebraMap k Γ(X, ⊤) r) := rfl

theorem toOm_smul_k (s : X ⟶ Sp k) (q : ℕ) (U : X.Opens) (r : k) (x : OmU s U q) :
    letI := algΓ s
    toOm s q U (r • x) = restrictGlobal X U (algebraMap k Γ(X, ⊤) r) • toOm s q U x := by
  letI := algΓ s
  rw [algebra_compatible_smul (Sec s U) r x, map_smul, algebraMap_sec_eq]
  rfl

def omSecEquiv (s : X ⟶ Sp k) (q : ℕ) (U : X.affineOpens) :
    letI := algΓ s
    OmU s U.1 q ≃ₗ[k] sectionsOn (Omega s q) U.1 :=
  letI := algΓ s
  { (toOmEquiv s q U.2).toAddEquiv.trans (sectionsOn.toΓ (Omega s q) U.1).symm with
    map_smul' := fun r x ↦ (sectionsOn.toΓ (Omega s q) U.1).injective (by
      change toOm s q U.1 (r • x) = _
      rw [toOm_smul_k, sectionsOn.toΓ_smul]
      rfl) }

theorem toΓ_omSecEquiv (s : X ⟶ Sp k) (q : ℕ) (U : X.affineOpens) (x : OmU s U.1 q) :
    letI := algΓ s
    sectionsOn.toΓ (Omega s q) U.1 (omSecEquiv s q U x) = toOm s q U.1 x := rfl

def omSecIso (s : X ⟶ Sp k) (q : ℕ) : OmF (OAff s) q ≅ affSec s q :=
  letI := algΓ s
  NatIso.ofComponents (fun U ↦ (omSecEquiv s q U.unop).toModuleIso) (fun {U V} a ↦ by
    ext x
    apply (sectionsOn.toΓ (Omega s q) V.unop.1).injective
    exact (res_toOm s q (leOfHom a.unop) x).symm)

theorem toΓ_omSecIso_hom (s : X ⟶ Sp k) (q : ℕ) (U : AffOp X) (x : OmU s U.unop.1 q) :
    letI := algΓ s
    sectionsOn.toΓ (Omega s q) U.unop.1 (((omSecIso s q).hom.app U).hom x) = toOm s q U.unop.1 x := rfl

section PairSec

variable {s : X ⟶ Sp k} {s' : X' ⟶ Sp k} {f : X' ⟶ X}

def pairSecMor (hf : f ≫ s = s') (q : ℕ) :
    GlobalTheory.CatH.Mor (affSec s q) (pairFst f ⋙ affSec s' q) (RingHom.id k) :=
  letI := algΓ s
  letI := algΓ s'
  { G := pairSnd f
    τ p := (sectionsOn.res k (Omega s' q) p.unop.2).comp
      (sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf q) p.unop.1.2.1)
    nat := fun {p p'} a x ↦
      (congrArg (sectionsOn.res k (Omega s' q) p'.unop.2) (sectionsOn.mapOver_res
        (appTop_algebraMap hf) (omegaPull hf q) (Pair.le_snd (leOfHom a.unop)) x)).trans
        ((sectionsOn.res_res k _ _ _ _).trans (sectionsOn.res_res k _ _ _ _).symm) }

theorem toΓ_pairSecMor (hf : f ≫ s = s') (q : ℕ) (p : (Pair f)ᵒᵖ)
    (x : (affSec s q).obj ((pairSnd f).obj p)) :
    letI := algΓ s
    letI := algΓ s'
    sectionsOn.toΓ (Omega s' q) p.unop.1.1.1 ((pairSecMor hf q).τ p x) =
      (Omega s' q).presheaf.map (homOfLE p.unop.2).op
        ((omegaPull hf q).app p.unop.1.2.1 (sectionsOn.toΓ (Omega s q) p.unop.1.2.1 x)) := rfl

end PairSec

end GlobalTheory.HodgeCoh
