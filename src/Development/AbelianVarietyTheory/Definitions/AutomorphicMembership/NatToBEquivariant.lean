import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicColimitOfIsNilpotent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ApolarMonomial

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.EigenSplit GlobalTheory.DeRham GlobalTheory.Cris
open Formalism.MainNotions.DIV.Cons (SCF intO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

section Contr

variable {O C Λ J : Type} [CommRing O] [Field C] [Algebra O C] [CommRing Λ] [DecidableEq J] {σ : J → Λ →+* C}
  (h : IsSplitting σ) {M M' : Type*} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']

def eigDefect (ρ : Λ →+* Module.End O M) (i : J) (x : M) : C ⊗[O] M :=
  proj h (baseChangeAction C ρ) i (1 ⊗ₜ x) - 1 ⊗ₜ x

def contr (ρ : Λ →+* Module.End O M) (ψ : LinearMap.BilinForm O M) (i : J) (x x' : M) : C :=
  ψ.baseChange C (eigDefect h ρ i x) (1 ⊗ₜ x')

end Contr

section Nat

variable {O Λ : Type} [CommRing O] [CommRing Λ] {G B : Over (Sp O)} [GrpObj G] [IsCommMonObj G] [GrpObj B]
  [IsCommMonObj B] {a : OAct Λ G} {b : OAct Λ B}

variable (b) in

structure PolSplit (L : LB B.left) : Type 1 where

  ψ : LinearMap.BilinForm O (HdR B)
  pol : IsPolForm (dp0 O) (𝟙 _) B L ψ

  s : Lie b →ₗ[O] HdR B
  lift : ∀ v, IsLieImage (s v) v.hom
  lag : ∀ v w, ψ (s v) (s w) = 0

variable {q : G ⟶ B} (hq : IsLinearHom a b q)

def NatLie (_hq : IsLinearHom a b q) : Submodule O (Lie a × HdR B) where
  carrier := {z | IsLieImage z.2 (z.1.hom ≫ q)}
  add_mem' {z w} hz hw := by
    haveI := _hq.isMonHom
    have := IsLieImage.add hz hw
    rwa [← MonObj.mul_comp] at this
  zero_mem' := by
    haveI := _hq.isMonHom
    change IsLieImage 0 ((1 : epsR O ⟶ G) ≫ q)
    rw [MonObj.one_comp]
    exact isLieImage_one_iff.2 (zero_mem _)
  smul_mem' r z hz := by
    have := IsLieImage.smul hz r
    rwa [← Category.assoc] at this

def natToB : NatLie hq →ₗ[O] HdR B := LinearMap.snd O _ _ ∘ₗ (NatLie hq).subtype

def natEnd (c : Λ) : Module.End O (NatLie hq) :=
  ((DistribSMul.toLinearMap O (Lie a) c).prodMap (DeRham.act (dp0 O) (𝟙 _) b c)).restrict fun z hz => by
    haveI := b.hom c
    have := IsLieImage.push hz (b.act c)
    rwa [Category.assoc, ← hq.comm, ← Category.assoc] at this

def natAct : Λ →+* Module.End O (NatLie hq) where
  toFun := natEnd hq
  map_one' := LinearMap.ext fun z => Subtype.ext (Prod.ext (one_smul Λ z.1.1)
    (LinearMap.congr_fun (map_one (DeRham.act (dp0 O) (𝟙 _) b)) z.1.2))
  map_mul' c c' := LinearMap.ext fun z => Subtype.ext (Prod.ext (mul_smul c c' z.1.1)
    (LinearMap.congr_fun (map_mul (DeRham.act (dp0 O) (𝟙 _) b) c c') z.1.2))
  map_zero' := LinearMap.ext fun z => Subtype.ext (Prod.ext (zero_smul Λ z.1.1)
    (LinearMap.congr_fun (map_zero (DeRham.act (dp0 O) (𝟙 _) b)) z.1.2))
  map_add' c c' := LinearMap.ext fun z => Subtype.ext (Prod.ext (add_smul c c' z.1.1)
    (LinearMap.congr_fun (map_add (DeRham.act (dp0 O) (𝟙 _) b) c c') z.1.2))

variable {L : LB B.left} (sp : PolSplit b L)

def natForm : LinearMap.BilinForm O (NatLie hq) := sp.ψ.compl₁₂ (natToB hq) (natToB hq)

def natLift (v : Lie a) : NatLie hq :=
  ⟨(v, sp.s (Lie.mapLinear hq v)), sp.lift (Lie.mapLinear hq v)⟩

variable {C J : Type} [Field C] [Algebra O C] [DecidableEq J] {σ : J → Λ →+* C} (h : IsSplitting σ)

def kapAb (i : J) (u u' : Lie b) : C := contr h (DeRham.act (dp0 O) (𝟙 _) b) sp.ψ i (sp.s u) (sp.s u')

def kapExt (i : J) (u u' : Lie a) : C :=
  contr h (natAct hq) (natForm hq sp) i (natLift hq sp u) (natLift hq sp u')

end Nat

end GlobalTheory.RayEv
