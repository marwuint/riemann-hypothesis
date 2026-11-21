import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.FlatModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

variable {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ : FrameFn Xo c} {a : c.F}

theorem epsMul_zero_comp {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {v : epsAt x ⟶ G} (hv : IsTanAt G x v) : spMap (epsMul (0 : R)) ≫ v.left = (1 : epsAt x ⟶ G).left := by
  have h0 : epsMul (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    ext z <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have h1 : spMap (epsMul (0 : R)) = spMap (algebraMap R (DualNumber R)) ≫
      spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    rw [h0, ← Spec.map_comp]; rfl
  rw [h1, Category.assoc]
  erw [hv]
  let k : epsAt x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R (DualNumber R))) rfl
  have := congrArg (fun t => t.left) (MonObj.comp_one k (M := G))
  exact this

theorem isComb_one {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {n : ℕ}
    {v : Fin n → (epsAt x ⟶ G)} (hv : ∀ i, IsTanAt G x (v i)) (i : Fin n) :
    IsComb ((1 : Matrix (Fin n) (Fin n) R) i) v (v i) := by
  classical
  refine ⟨fun j => if i = j then v j else 1, fun j => ?_, ?_⟩
  · by_cases h : i = j
    · have h1 : epsMul (1 : R) = RingHom.id _ := by ext z <;> simp [epsMul]
      simp [h, Matrix.one_apply, h1, spMap]
    · simp only [h, Matrix.one_apply, if_false]
      exact (epsMul_zero_comp (hv j)).symm
  · induction n with
    | zero => exact i.elim0
    | succ n ih =>
      rw [List.ofFn_succ, List.prod_cons]
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [List.prod_eq_one, (Fin.succ_ne_zero _).symm]
      · simp only [Fin.succ_ne_zero, if_false, _root_.one_mul, Fin.succ_inj]
        exact ih (v := fun j => v j.succ) (fun j => hv _) i

end GlobalTheory.CompanionTheory.Ar.Fl.FlatModel
