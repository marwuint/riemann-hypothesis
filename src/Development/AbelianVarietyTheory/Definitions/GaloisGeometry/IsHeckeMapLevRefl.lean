import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRankOneIdem
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFullSetCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetIsHeckeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtModelForgetFiniteEtale

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory GlobalTheory.AV GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo

namespace GlobalTheory.DrinLev.HT

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

namespace LevRep

variable {N : ℕ} {w : Ideal (𝓞 D.F)} {m : ℕ} {e : D.O}

def univAct (M : LevRep b N w m e) (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) : ObjLev b N w m e M.s :=
  ⟨M.univ.obj, GlobalTheory.LevDict.htLevelAct M.univ.lev g⟩

def levAct (M : LevRep b N w m e) (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) : M.X ⟶ M.X :=
  (M.rep M.X M.s (M.univAct g)).exists.choose

variable (M : LevRep b N w m e)

theorem levAct_spec (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) :
    M.levAct g ≫ M.s = M.s ∧ ObjLevMap (M.univAct g) M.univ (M.levAct g) :=
  (M.rep M.X M.s (M.univAct g)).exists.choose_spec

@[simp] theorem levAct_comp_s (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) : M.levAct g ≫ M.s = M.s := (M.levAct_spec g).1

theorem eq_levAct (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) (f : M.X ⟶ M.X) (h₁ : f ≫ M.s = M.s)
    (h₂ : ObjLevMap (M.univAct g) M.univ f) : f = M.levAct g :=
  (M.rep M.X M.s (M.univAct g)).unique ⟨h₁, h₂⟩ (M.levAct_spec g)

@[simp] theorem levAct_one : M.levAct 1 = 𝟙 M.X := by
  refine (M.eq_levAct 1 (𝟙 _) (Category.id_comp _) ⟨GlobalTheory.UPel.HT.EtLev.LevForget.idMap M.univ.obj, fun x => ?_⟩).symm
  show (M.univ.lev.α ((1 : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)).val.mulVec x)).left ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp

theorem levAct_mul (h g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) :
    M.levAct (h * g) = M.levAct h ≫ M.levAct g := by
  symm
  obtain ⟨φh, hh⟩ := (M.levAct_spec h).2
  obtain ⟨φg, hg⟩ := (M.levAct_spec g).2
  have hh' : ∀ y, (M.univ.lev.α (h.val.mulVec y)).left ≫ φh.φ = M.levAct h ≫ (M.univ.lev.α y).left := hh
  have hg' : ∀ y, (M.univ.lev.α (g.val.mulVec y)).left ≫ φg.φ = M.levAct g ≫ (M.univ.lev.α y).left := hg
  refine M.eq_levAct (h * g) _ (by rw [Category.assoc, levAct_comp_s, levAct_comp_s]) ⟨ObjMap.comp φh φg, fun x => ?_⟩
  have e1 : (h * g).val.mulVec x = h.val.mulVec (g.val.mulVec x) := by rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  show (M.univ.lev.α ((h * g).val.mulVec x)).left ≫ (φh.φ ≫ φg.φ) = (M.levAct h ≫ M.levAct g) ≫ _
  rw [e1]
  erw [← Category.assoc, hh', Category.assoc, hg']
  simp only [Category.assoc]

@[simp] theorem levAct_inv_comp (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) : M.levAct g⁻¹ ≫ M.levAct g = 𝟙 M.X := by
  rw [← levAct_mul, inv_mul_cancel, levAct_one]

@[simp] theorem levAct_comp_inv (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) : M.levAct g ≫ M.levAct g⁻¹ = 𝟙 M.X := by
  rw [← levAct_mul, mul_inv_cancel, levAct_one]

@[simp] theorem levAct_forget (F₀ : RepFam b N) (g : GL (Fin D.n) (𝓞 D.F ⧸ w ^ m)) :
    M.levAct g ≫ M.forget F₀ = M.forget F₀ := by
  have hf := (F₀.rep M.X M.s M.univ.obj).exists.choose_spec
  obtain ⟨φg, -⟩ := (M.levAct_spec g).2
  exact (F₀.rep M.X M.s M.univ.obj).unique
    ⟨by rw [Category.assoc]; erw [hf.1]; exact M.levAct_comp_s g, ⟨ObjMap.comp φg hf.2.some⟩⟩ hf

end LevRep

end GlobalTheory.DrinLev.HT
