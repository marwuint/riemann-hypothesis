import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackOfIsOpenImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoSeq

section General

variable {O : Type} [CommRing O] {X T T' S : Scheme.{0}} {A B A' B' : X.Modules}

def sqIso {b : S ⟶ T} {a : T ⟶ X} {c : S ⟶ T'} {a' : T' ⟶ X} (w : b ≫ a = c ≫ a') :
    Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback b ≅ Scheme.Modules.pullback a' ⋙ Scheme.Modules.pullback c :=
  Scheme.Modules.pullbackComp b a ≪≫ Scheme.Modules.pullbackCongr w ≪≫ (Scheme.Modules.pullbackComp c a').symm

structure Datum (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ) where

  D : X.Modules

  ρ : O →+* End D

  a : A ⟶ D

  b : D ⟶ B

  u : A' ⟶ D

  v : D ⟶ B'
  w₁ : a ≫ b = 0
  w₂ : u ≫ v = 0
  isVB : IsVB D r
  exact₁ : (ShortComplex.mk a b w₁).ShortExact
  exact₂ : (ShortComplex.mk u v w₂).ShortExact
  equiv_a : IsEquivariant α ρ a
  equiv_b : IsEquivariant ρ β b
  equiv_u : IsEquivariant α' ρ u
  equiv_v : IsEquivariant ρ β' v

variable (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ)

variable {α β α' β' r}

def biprodAct (α : O →+* End A) (β : O →+* End B) : O →+* End (A ⊞ B) where
  toFun x := biprod.map (act α x) (act β x)
  map_one' := by
    rw [act, act, map_one, map_one]
    exact biprod.hom_ext _ _ (by simp [End.one_def]) (by simp [End.one_def])
  map_mul' x y := by
    rw [act, act, map_mul, map_mul]
    exact biprod.hom_ext _ _ (by simp [End.mul_def]) (by simp [End.mul_def])
  map_zero' := by
    rw [act, act, map_zero, map_zero]
    change (biprod.map (0 : A ⟶ A) (0 : B ⟶ B) : A ⊞ B ⟶ A ⊞ B) = (0 : A ⊞ B ⟶ A ⊞ B)
    exact biprod.hom_ext _ _ (by simp) (by simp)
  map_add' x y := by
    rw [act, act, map_add, map_add]
    change (biprod.map (act α x + act α y) (act β x + act β y) : A ⊞ B ⟶ A ⊞ B) =
      (biprod.map (act α x) (act β x) + biprod.map (act α y) (act β y) : A ⊞ B ⟶ A ⊞ B)
    exact biprod.hom_ext _ _ (by simp) (by simp)

def Datum.split (α : O →+* End A) (β : O →+* End B) {m n : ℕ} (hA : IsVB A m) (hB : IsVB B n) :
    Datum α β β α (m + n) where
  D := A ⊞ B
  ρ := biprodAct α β
  a := biprod.inl
  b := biprod.snd
  u := biprod.inr
  v := biprod.fst
  w₁ := by simp
  w₂ := by simp
  isVB := hA.biprod hB
  exact₁ := (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact
  exact₂ := (ShortComplex.Splitting.mk (S := ShortComplex.mk (biprod.inr : B ⟶ A ⊞ B) biprod.fst (by simp))
    biprod.snd biprod.inl (by simp) (by simp) (by rw [add_comm]; exact biprod.total)).shortExact
  equiv_a x := by simp [act, biprodAct]
  equiv_b x := by simp [act, biprodAct]
  equiv_u x := by simp [act, biprodAct]
  equiv_v x := by simp [act, biprodAct]

end General

end GlobalTheory.TwoSeq
