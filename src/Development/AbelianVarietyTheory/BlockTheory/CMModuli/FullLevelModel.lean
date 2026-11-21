import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FullLevelModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure PModel (H : Host E) (O : Type) [CommRing O] where
  X : Scheme.{0}
  s : X ⟶ Sp O
  normal : IsNormalScheme X
  proj : IsProjOver s
  flat : Flat s
  t : SAB H X

def w0C (H : Host E) : ℂ := (1 + H.rt0) / 2

def oRing (H : Host E) (N c : ℕ) : Subring ℂ := Subring.closure {w0C H, zeta N, (c : ℂ)⁻¹}

def oLoc (H : Host E) (p N : ℕ) : Subring ℂ :=
  Subring.closure ({w0C H} ∪ ({zeta N} ∪ {x | ∃ k : ℕ, k.Coprime p ∧ x = (k : ℂ)⁻¹}))

def oW (H : Host E) (N c : ℕ) : oRing H N c := ⟨w0C H, Subring.subset_closure (by simp)⟩

def oZeta (H : Host E) (N c : ℕ) : oRing H N c := ⟨zeta N, Subring.subset_closure (by simp)⟩

def oRt (H : Host E) (N c : ℕ) : oRing H N c := 2 * oW H N c - 1

theorem oRing_le_oLoc (p N n : ℕ) (h : n.Coprime p) : oRing H N n ≤ oLoc H p N := by
  refine Subring.closure_le.2 ?_
  rintro x (rfl | rfl | rfl)
  · exact Subring.subset_closure (Or.inl rfl)
  · exact Subring.subset_closure (Or.inr (Or.inl rfl))
  · exact Subring.subset_closure (Or.inr (Or.inr ⟨n, h, rfl⟩))

theorem ZP_le_oLoc (p N : ℕ) : ZP p N ≤ oLoc H p N := Subring.closure_mono Set.subset_union_right

structure FullObj (D : Datum H) (N : ℕ) {B : Type} [CommRing B] (ρ ζ : B) {S : Scheme.{0}} (s : S ⟶ Sp B) where
  t : SAB H S
  proper : IsProper t.G.hom
  ample : Out.RelAmple t.G t.PP.L
  ktriv : Out.KTriv t.G t.PP.L
  lev : D.La → (𝟙_ (Over S) ⟶ t.G)
  lev_add : ∀ a c, lev (a + c) = lev a * lev c
  lev_lin : ∀ (c : 𝓞 E) a, lev (c • a) = lev a ≫ t.act.act c
  lev_ker : ∀ a, lev (N • a) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (z : kˣ), x ≫ s = spMap β →
    (z : k) = β ζ →
    (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = N • b)) ∧
    (∀ g : Over.mk x ⟶ t.G, g ^ N = 1 → ∃ a, toUnit _ ≫ lev a = g) ∧
    ∀ a b, Out.WeilIs t.G t.PP.L N (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ D.EF a b))
  geom0 : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
    DetCond D t.act x (β ρ) ∧
    ∃ I : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
      (I.ζ N : k) = β ζ ∧ ∀ a, toUnit _ ≫ lev a = I.ev N a

structure FullMap {D : Datum H} {N : ℕ} {B : Type} [CommRing B] {ρ ζ : B} {S' S : Scheme.{0}} {s' : S' ⟶ Sp B}
    {s : S ⟶ Sp B} (o' : FullObj D N ρ ζ s') (o : FullObj D N ρ ζ s) (f : S' ⟶ S) extends SABMap o'.t o.t f where
  lev : ∀ a, (o'.lev a).left ≫ cm.F = f ≫ (o.lev a).left

def gDim (D : Datum H) : ℕ := Module.finrank ℚ E / 2 * (D.p + D.q)

structure FullPre (D : Datum H) (N n : ℕ) extends PModel H (oRing H N n) where
  U : X.Opens
  U_eq : (U : Set X) = abLocus t.G
  U_dense : Dense (U : Set X)
  ab : FullObj D N (oRt H N n) (oZeta H N n) (U.ι ≫ s)
  mU : SABMap ab.t t U.ι

namespace FullPre

end FullPre

variable {D : Datum H}

variable {Xo : ∀ l : Level H, Moduli D l} {n J : ℕ}

end GlobalTheory.IndefiniteRowSideFullHecke.FullLevelModel
