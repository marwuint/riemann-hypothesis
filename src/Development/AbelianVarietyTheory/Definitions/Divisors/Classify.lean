import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ClassifyField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

section Points

variable {R : Type} [CommRing R] {b : Base D R} {k : Type} [Field k] {β : R →+* k} {N N' : ℕ} (L : Link D G)

def raw {A : Type} [Ring A] [Algebra ℚ A] (o : Obj b N (spMap β)) (ia : A →ₐ[ℚ] End0 (av o)) : GlobalTheory.LKP.Raw k A where
  A := av o
  ia := ia
  L := o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left
  hL := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull o.isLB _

variable [CharP k p] [PerfectRing k p]

abbrev OFrame (T : Theory p) (red : (Obar p).toSubring →+* k) (r : ℕ) (o : Obj b N (spMap β)) (π : End0 (av o))
    (H : PDivGroup p k) (t : H.TorsionTower (av o).X) (d : (w : Fin G.m) → GL (Fin G.n) (KQ p (G.Fw w) r)) : Type :=
  Frame L T red r H (fun c => t.map t (actEnd o c).hom)
    (fun m ψ => ∃ g : End (av o), m • π = toEnd0 _ g ∧ ψ = t.map t g.hom) d

def RowRel (r : ℕ) (w : Fin G.m) (c : ℤ) (u : GL (Fin G.n) (KQ p (G.Fw w) r))
    (X Y : Matrix (Fin D.m) (Fin G.n) (intKQ p (G.Fw w) r)) : Prop :=
  Y.map (intKQ p (G.Fw w) r).subtype =
    c • HMul.hMul (α := Matrix (Fin D.m) (Fin G.n) (KQ p (G.Fw w) r)) (β := Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r))
      (X.map (intKQ p (G.Fw w) r).subtype) u.val

structure Based (T : Theory p) (red : (Obar p).toSubring →+* k) (r : ℕ) (P : Pair G) (o : Obj b N (spMap β))
    (π : End0 (av o)) where

  I : TIso o
  ind : Induces o I

  x : (AfP p ⊗[ℚ] G.C)ˣ

  s : (AfP p)ˣ
  hx : Triv G (AfP p) P.β x s

  δ : Gr G r

  z : Gr G r
  nrm : IsNrm G r P.atP δ z
  supp : L.MuSupp r δ

  j : P.cent →* (End0 (av o))ˣ
  j_self : (j P.self : End0 (av o)) * π = 1
  j_af : ∀ y, ActsQ L I (j y : End0 (av o)) (P.toAf x s hx y)
  j_surj : ∀ u : End0 (av o), Commute u π → (∃ g, ActsQ L I u g) → ∃ y, (j y : End0 (av o)) = u

  H : PDivGroup p k

  t : H.TorsionTower (av o).X

  fr : OFrame L T red r o π H t δ.2
  j_p : ∀ y (m : ℤ) (ψ : End (av o)), m • (j y : End0 (av o)) = toEnd0 _ ψ → ∀ w X Y,
    RowRel r w m ((P.toQr r z y).2 w) X Y → T.map (t.map t ψ.hom) (fr.B w X) = fr.B w Y

variable {L}

end Points

structure Chart (L : Link D G) (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra G.F M] where
  rank : Module.finrank G.F M = G.n

  i : M →ₐ[G.F] G.C

  H : Fin G.n → M
  pos : ∀ a, GlobalTheory.LKP.TotPos (H a)

  κ : VQ D ≃ₗ[ℚ] (Fin G.n → M)
  κ_i : ∀ x v, κ (L.rep (i x) v) = x • κ v

  oM : D.O →+* Matrix (Fin G.n) (Fin G.n) M
  κ_o : ∀ c v, κ (actQ D c v) = oM c *ᵥ κ v
  span : Submodule.span M (Set.range oM) = ⊤
  star : ∀ c, oM (D.star c).unop = GlobalTheory.LKP.sigH H (oM c)

namespace Chart

end Chart

end GlobalTheory.LKGeo
