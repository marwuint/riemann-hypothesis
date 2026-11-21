import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleSheaf
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh

noncomputable section

universe u

section VectorBundle

variable {X : Scheme.{u}}

def IsFreeBasisOn (P : PMod X) (U : X.Opens) {n : ℕ} (s : Fin n → P.obj (op U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U), Function.Bijective
    (fun r : Fin n → ringOn X V => ∑ i, r i • resM P h (s i))

def IsVectorBundle (E : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ (n : ℕ) (s : Fin n → ((preMod X).obj E).obj (op U)), IsFreeBasisOn ((preMod X).obj E) U s

end VectorBundle

section OverZ

def toSpecZ (X : Scheme.{0}) : X ⟶ Spec (.of ℤ) := specZIsTerminal.from X

theorem specZ_hom_ext {X : Scheme.{0}} (f g : X ⟶ Spec (.of ℤ)) : f = g :=
  specZIsTerminal.hom_ext f g

def invOpen (X : Scheme.{0}) (m : ℕ) : X.Opens :=
  toSpecZ X ⁻¹ᵁ (PrimeSpectrum.basicOpen (m : ℤ) : (Spec (.of ℤ)).Opens)

instance (p : Nat.Primes) : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)

abbrev ZLoc (p : Nat.Primes) : Type := Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})

def zLocToRat (p : Nat.Primes) : ZLoc p →+* ℚ :=
  IsLocalization.lift (M := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl) (g := algebraMap ℤ ℚ) (by
    rintro ⟨y, hy⟩
    refine isUnit_iff_ne_zero.mpr ?_
    intro h0
    apply hy
    have : y = 0 := by simpa using h0
    rw [this]
    exact Ideal.zero_mem _)

def atP (X : Scheme.{0}) (p : Nat.Primes) : Scheme.{0} :=
  pullback (toSpecZ X) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZLoc p))))

def genFib (X : Scheme.{0}) : Scheme.{0} :=
  pullback (toSpecZ X) (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))

def genTo (X : Scheme.{0}) : genFib X ⟶ X := pullback.fst _ _

def genToAtP (X : Scheme.{0}) (p : Nat.Primes) : genFib X ⟶ atP X p :=
  pullback.map _ _ _ _ (𝟙 X) (Spec.map (CommRingCat.ofHom (zLocToRat p))) (𝟙 _)
    (specZ_hom_ext _ _) (specZ_hom_ext _ _)

end OverZ

section Pullbacks

variable {A B C D : Scheme.{u}}

def pbSection (f : A ⟶ B) (M : B.Modules) (t : Γ(M, ⊤)) :
    Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ ⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤) t

end Pullbacks

section Opens

def primeProd (S : Finset Nat.Primes) : ℕ := ∏ p ∈ S, (p : ℕ)

def genOpen (X : Scheme.{0}) (m : ℕ) : (genFib X).Opens := genTo X ⁻¹ᵁ invOpen X m

def genRes (X : Scheme.{0}) (m : ℕ) : (genOpen X m).toScheme ⟶ (invOpen X m).toScheme :=
  genTo X ∣_ invOpen X m

end Opens

section Unit

variable {X Y : Scheme.{u}}

instance final_opensMap (f : X ⟶ Y) : (Opens.map f.base).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun _ => ⟨⊤, ⟨homOfLE le_top⟩⟩)
    (fun _ _ => ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)

end Unit

section SchemeStatements

structure GlueBundles.Data (X : Scheme.{0}) (S : Finset Nat.Primes) where

  E₀ : (invOpen X (primeProd S)).toScheme.Modules
  isVB₀ : IsVectorBundle E₀

  E : ∀ p : S, (atP X p).Modules
  isVB : ∀ p : S, IsVectorBundle (E p)

  γ : ∀ p : S, (Scheme.Modules.pullback ((genOpen X (primeProd S)).ι ≫ genToAtP X p)).obj (E p) ≅
    (Scheme.Modules.pullback (genRes X (primeProd S))).obj E₀

end SchemeStatements

section AlgebraStatements

def Dominates (A : Type*) {K : Type*} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]
    (V : Subring K) : Prop :=
  ∃ h : ∀ a : A, algebraMap A K a ∈ V,
    ∀ a : A, (⟨_, h a⟩ : V) ∈ nonunits V ↔ a ∈ IsLocalRing.maximalIdeal A

def blowUpChart (A K : Type*) [CommRing A] [Field K] [Algebra A K] {n : ℕ} (x : Fin n → A)
    (i : Fin n) : Subalgebra A K :=
  Algebra.adjoin A (Set.range fun j => algebraMap A K (x j) / algebraMap A K (x i))

end AlgebraStatements

section NumberStatements

def MertensUpper.Statement : Prop :=
  ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B →
    ∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊B⌋₊ + 1)), Real.log p / p ≤ Real.log B + C

def cp (p : ℕ) : ℝ := if p = 2 then 2 else 1 / ((p : ℝ) - 1)

end NumberStatements

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
