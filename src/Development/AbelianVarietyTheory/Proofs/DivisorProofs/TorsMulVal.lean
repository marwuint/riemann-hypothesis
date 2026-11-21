import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus
open GlobalTheory.DeRham (spOver spOver_comp)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

variable {R : Type} [CommRing R]

section Tors

variable {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ}

instance torsGroup (B : Type) [CommRing B] [Algebra R B] : CommGroup (Tors G N B) :=
  inferInstanceAs (CommGroup (powMonoidHom N : (SpAlg R B ⟶ G) →* (SpAlg R B ⟶ G)).ker)

@[simp] theorem tors_mul_val {B : Type} [CommRing B] [Algebra R B] (x y : Tors G N B) : (x * y).1 = x.1 * y.1 := rfl

@[simp] theorem tors_one_val {B : Type} [CommRing B] [Algebra R B] : (1 : Tors G N B).1 = 1 := rfl

def torsMap {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C) (z : Tors G N B) :
    Tors G N C :=
  ⟨spOver φ ≫ z.1, by rw [← MonObj.comp_pow, z.2, MonObj.comp_one]⟩

@[simp] theorem torsMap_val {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C)
    (z : Tors G N B) : (torsMap φ z).1 = spOver φ ≫ z.1 := rfl

end Tors

section Pts

variable (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ)

structure TorsPt (A : Type) [CommRing A] [HopfAlgebra R A] : Type 1 where

  pt : ∀ (B : Type) [CommRing B] [Algebra R B], Tors G N B → (A →ₐ[R] B)

  nat : ∀ (B C : Type) [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C) (z : Tors G N B),
    pt C (torsMap φ z) = φ.comp (pt B z)

  mul : ∀ (B : Type) [CommRing B] [Algebra R B] (x y : Tors G N B),
    toConv (pt B (x * y)) = toConv (pt B x) * toConv (pt B y)

variable {G N} {A : Type} [CommRing A] [HopfAlgebra R A]

structure IsLevel (K : Type) [Field K] [Algebra R K] (θ : TorsPt G N A) : Prop where

  opn : ∃ V : (Sp A).Opens, ∀ (B : Type) [CommRing B] [Algebra R B],
    Set.BijOn (θ.pt B) Set.univ {φ | Set.range (spMap (φ : A →+* B)) ⊆ V}

  gen : Function.Bijective (θ.pt K)

end Pts

section Chart

variable (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ)

structure PreChart (q : PrimeSpectrum R) : Type 1 where

  r : R
  hr : r ∉ q.asIdeal

  C : Type
  [ring : CommRing C]
  [alg : Algebra R C]
  [algLoc : Algebra (Localization.Away r) C]
  [tower : IsScalarTower R (Localization.Away r) C]
  [finite : Module.Finite (Localization.Away r) C]
  [free : Module.Free (Localization.Away r) C]

  j : Tors G N C

  W : G.left.Opens

  bij : ∀ (B : Type) [CommRing B] [Algebra R B],
    Set.BijOn (fun ψ : C →ₐ[R] B => torsMap ψ j) Set.univ {z | Set.range z.1.left ⊆ W}

  fibre : ∀ (k : Type) [Field k] [Algebra R k], RingHom.ker (algebraMap R k) = q.asIdeal →
    ∀ z : Tors G N k, Set.range z.1.left ⊆ W

attribute [instance] PreChart.ring PreChart.alg PreChart.algLoc PreChart.tower PreChart.finite PreChart.free

variable {G N}

end Chart

end GlobalTheory.GroupBplus.Aff
