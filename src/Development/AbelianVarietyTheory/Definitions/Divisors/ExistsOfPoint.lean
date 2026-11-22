import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

structure TautBase (o : Type) [CommRing o] (W : Type) [CommRing W] [IsLocalRing W] where

  b : o →+* W

  B : Over (Sp W)
  [grp : GrpObj B]
  [comm : IsCommMonObj B]
  isAb : IsAbelianScheme B

  g : ℕ
  smoothDim : SmoothOfRelativeDimension g B.hom

  M : RigLB B

  cub : CubicalStr B M
  ample : RelAmple B M.L
  ktriv : KTriv B M.L

  r : ℕ

  c₀ : (Fin r → ℤ) → (𝟙_ (Over (Sp W)) ⟶ B)
  c₀_add : ∀ a a', c₀ (a + a') = c₀ a * c₀ a'

  τ₀ : ∀ a a' : Fin r → ℤ, LB.Gen (LB.LinComb M.L (lamPts (c₀ a) (c₀ a')) negε)
  τ₀_gen : ∀ a a', (τ₀ a a').IsGen
  τ₀_symm : ∀ a a' z J, Good M.L z J → val (τ₀ a a') (𝟙 _) z J = val (τ₀ a' a) (𝟙 _) z J
  τ₀_add : ∀ a a' a'' z J, Good M.L z J →
    val (τ₀ (a + a') a'') (𝟙 _) z J * cubV cub z J (c₀ a) (c₀ a') (c₀ a'') =
      val (τ₀ a a'') (𝟙 _) z J * val (τ₀ a' a'') (𝟙 _) z J

attribute [instance] TautBase.grp TautBase.comm

theorem TautBase.c₀_zero {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) : T.c₀ 0 = 1 := by
  have h := T.c₀_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

end GlobalTheory.PolDeg
