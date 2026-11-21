import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def IsTrAt {R : Type} [CommRing R] (x : KeyIn R) (m : ℕ) (z : Sp R ⟶ x.P.A.left) (s : (lbPow x.P.L (m ^ 2)).Sec) : Prop :=
  ∃ th U t, IsPolAVSectionInverseImage x.P (baseOver (Sp R)) x.th th ∧ FinOrdT x.P U ∧ Tr x.P x.rig m th U t ∧
    OnT x.P (baseOver (Sp R)) (m ^ 2) s t ∧ U.pt.left = z

structure PB {K K' : Type} [Field K] [Field K'] (x : KeyIn K) (f : K →+* K') where

  x' : KeyIn K'
  hg : x'.P.g = x.P.g

  ψ : x'.P.A.left ⟶ x.P.A.left
  key : KeyPB x' x f
  fib : IsPolFibre f x.P x'.P ψ
  vec : ∀ i, IsVecOver f ψ (x.v (i.cast hg)) (x'.v i)

  w : ∀ n, LB.Iso ((lbPow x.P.L n).pull ψ) (lbPow x'.P.L n)
  gen : ∀ n, (w n).IsGen
  rig : ∀ (n : ℕ) (i : x.P.L.ι) (i' : x'.P.L.ι), ⊤ ≤ (eSec x.P.A) ⁻¹ᵁ x.P.L.U i → ⊤ ≤ (eSec x'.P.A) ⁻¹ᵁ x'.P.L.U i' →
    valR (X := x'.P.A.left) (eSec x'.P.A) _ ((w n).s (fun _ => i', fun _ _ => i)).val *
      f (valR (X := Sp K) (𝟙 _) _ (x.rig.s fun _ => i).val) ^ n =
      valR (X := Sp K') (𝟙 _) _ (x'.rig.s fun _ => i').val ^ n
  tr : ∀ (m : ℕ) z s, IsTrAt x m z s → ∃ z' s', z' ≫ ψ = spMap f ≫ z ∧ IsTrAt x' m z' s' ∧ SecMaps (w (m ^ 2)) (secPull s ψ) s'

structure Cx {K : Type} [Field K] (x : KeyIn K) (σ : K →+* ℂ) extends PB x σ where

  u : HolUnif x'.P.A x'.P.L x'.P.g

  Hm : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ

  χ : u.Λ → ℂ

  W : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ

  θ : (Fin x'.P.g → ℂ) → ℂ

  Fd : Set (Fin x'.P.g → ℂ)

  Ef : LinearMap.BilinForm ℤ u.Λ
  ah : u.IsAH Hm χ
  isRig : u.IsRig x'.rig
  fn : u.IsFn x'.th θ
  theta : u.IsThetaFn Hm χ 1 θ
  diff : ∀ i, u.IsDiff (W i) (x'.v i)
  fd : IsAddFundamentalDomain u.Λ Fd volume
  ef : ∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im
  efb : Function.Bijective Ef
  secs : ∀ (n : ℕ) s, ∃! Θ, u.IsThetaFn Hm χ n Θ ∧ u.IsFnPow n s Θ

end GlobalTheory.MBLow

end
