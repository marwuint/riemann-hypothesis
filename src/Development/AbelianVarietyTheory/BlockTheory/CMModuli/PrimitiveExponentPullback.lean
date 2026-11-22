import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.HostConjugateIdeal

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback

open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal

section Mumford

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

abbrev LamK : Type := ULift.{0} (Finset (Fin 2))

def lamPt {T : Over S} (x z : T ⟶ G) : LamK → (T.left ⟶ G.left) :=
  fun I => (psum G ![x, z] I.down).left

def lamExp : LamK → ℤ := fun I => (-1) ^ (2 - I.down.card)

def lamAt (L : LB G.left) {T : Over S} (x z : T ⟶ G) : LB T.left :=
  LB.LinComb L (lamPt G x z) lamExp

def adjPt (a b : G ⟶ G) : LamK ⊕ LamK → ((G ⊗ G).left ⟶ G.left) :=
  Sum.elim (lamPt G (fst G G) (snd G G ≫ b)) (lamPt G (fst G G ≫ a) (snd G G))

def adjExp : LamK ⊕ LamK → ℤ := Sum.elim lamExp (fun I => -lamExp I)

def IsAdjointPair (L : LB G.left) (a b : G ⟶ G) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L (adjPt G a b) adjExp), t.IsGen ∧
    LB.Gen.Corr L _ _ _ _
      (LB.pullGen L (adjPt G a b) adjExp t (lift (pzero G G) (𝟙 G)).left) (LB.oneGen L) ∧
    LB.Gen.Corr L _ _ _ _
      (LB.pullGen L (adjPt G a b) adjExp t (lift (𝟙 G) (pzero G G)).left) (LB.oneGen L)

def primPt (w : G ⟶ G) : PUnit.{1} ⊕ LamK → (G.left ⟶ G.left) :=
  Sum.elim (fun _ => 𝟙 G.left) (lamPt G (𝟙 G) w)

def primExp : PUnit.{1} ⊕ LamK → ℤ := Sum.elim (fun _ => 1) (fun I => -lamExp I)

def IsPrimitiveFor (L : RigLB G) (w : G ⟶ G) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L.L (primPt G w) primExp), t.IsGen ∧
    LB.Gen.Corr L.L _ _ (fun _ : PUnit.{1} => eSec G) (fun _ => 1)
      (LB.pullGen L.L (primPt G w) primExp t (eSec G)) L.rig

end Mumford

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

structure Triple (H : Host E) (S : Scheme.{0}) where

  G : Over S
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semiAbelian : IsSemiAbelian G

  iota : OAct (𝓞 E) G

  L : RigLB G

  cube : CubicalStr G L
  symm : L.IsSymmetric
  adjoint : ∀ a : 𝓞 E, IsAdjointPair G L.L (iota.act a) (iota.act (conjO E a))
  primitive : IsPrimitiveFor G L (iota.act H.w₀)

attribute [instance] Triple.grp Triple.comm

namespace Triple

variable {H : Host E} {S S' : Scheme.{0}}

def P (t : Triple H S) : LB (t.G ⊗ t.G).left := abelian₂ t.G t.L.L

structure Pull (t' : Triple H S') (t : Triple H S) (f : S' ⟶ S) where

  φ : t'.G.left ⟶ t.G.left
  isGrpPullback : IsGrpPullback t'.G t.G f φ
  act_comm : ∀ a : 𝓞 E, (t'.iota.act a).left ≫ φ = φ ≫ (t.iota.act a).left
  bundle : ∃ m : CubeMap t'.G t.G, m.F = φ ∧ m.e = f ∧ m.IsPullCubical t'.cube t.cube

end Triple

end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
