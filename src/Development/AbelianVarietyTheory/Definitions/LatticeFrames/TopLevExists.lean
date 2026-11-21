import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.Top.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word}

theorem unit_transfer {A B m n : Type} [CommRing A] [CommRing B] [Fintype m] [Fintype n] (e : m ≃ n) (s : A →+* B) (σ : A →+* A)
    (τ : B →+* B) (hs : ∀ x, s (σ x) = τ (s x)) (J : Matrix n n A) (J' : Matrix m m B) (hJ : ∀ a b, J' a b = s (J (e a) (e b)))
    (y : Matrix n n A) (g : Matrix m m B) (hg : ∀ a b, g a b = s (y (e a) (e b))) (hy : Formalism.UG.cT σ y * J * y = J) :
    Formalism.UG.cT τ g * J' * g = J' := by
  ext i j
  have := congrArg s (congrFun (congrFun hy (e i)) (e j))
  rw [hJ, ← this]
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hg, hJ, hs]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← e.sum_comp]

theorem swap_inj : Function.Injective (Lev.swapAE D) :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective

theorem hasMat_pt {h h' : GA D D.sp.X'} {y} (h1 : HasMat h y) (h2 : HasMat h' y) : h = h' := by
  refine GlobalTheory.UnitarySplit.ga_ext _ ?_ ?_
  · have a : infHom D.sp.X' h = 1 := h1.1
    have b : infHom D.sp.X' h' = 1 := h2.1
    rw [a, b]
  · apply Units.ext
    ext i j
    apply swap_inj
    exact (h1.2 i j).trans (h2.2 i j).symm

set_option maxHeartbeats 1000000 in

theorem hasMat_exists (y : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ h : GA D D.sp.X', HasMat h y.1 := by
  let e := finCongr (rankP D)
  let s := (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm
  let r := (Matrix.reindexAlgEquiv D.host.F (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) e.symm)
  let g := Formalism.UG.bc s.toRingEquiv.toRingHom (Units.map r.toRingEquiv.toRingHom.toMonoidHom y.1)
  have hg : ∀ i j, g.1 i j = s (y.1.1 (e i) (e j)) := fun i j => rfl
  have hm : g ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig D.sp.X'.gram := by
    have hs : ∀ x, s (Formalism.UG.sigR (sigD D) _ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig (s x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    have hy : Formalism.UG.cT (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) y.1.1 *
        (gramP D).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * y.1.1 =
        (gramP D).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := y.2
    have hJ : ∀ a b, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.X'.gram a b =
        s.toRingEquiv.toRingHom (((gramP D).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) (e a) (e b)) :=
      fun a b => rfl
    have key := unit_transfer e s.toRingEquiv.toRingHom (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) hs _ _ hJ y.1.1 g.1 hg hy
    exact key
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue D.sp.X' 1 g (one_mem _) hm
  refine ⟨k, k1, fun i j => ?_⟩
  rw [k2]
  exact s.symm_apply_apply _

theorem valC_ne_bot {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) : ValC G lam ≠ ⊥ := by
  intro h
  have hm : fnOf G (shiftOf lam) 1 (ten fun τ => extremal ℂ n (lam τ)) ∈ ValC G lam :=
    ⟨_, Submodule.subset_span ⟨_, fun τ => Submodule.subset_span ⟨[], rfl⟩, rfl⟩, rfl⟩
  rw [h, Submodule.mem_bot] at hm
  have := congrFun hm ⟨fun _ => 1, fun _ => by simp⟩
  simp [fnOf, ten, extremal, Formalism.GradedWeylDivisibility.hw, Formalism.GradedWeylDivisibility.lpMinor, MvPolynomial.eval_rename, RingHom.map_det] at this
  have e : ∀ (x : ι) (s : ℕ) (h1 h2 : s ≤ n), ((Matrix.of fun p q : Fin s => (MvPolynomial.X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin n × Fin n) ℂ)).map
      ⇑(MvPolynomial.eval ((fun x : ι × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) x.2.1 x.2.2) ∘ Prod.mk x))) = 1 := by
    intro x s h1 h2
    ext p q
    simp [Matrix.one_apply]
  simp only [e, Matrix.det_one, one_pow, Finset.prod_const_one] at this
  exact one_ne_zero this

end GlobalTheory.Core.Rk.Top.Model

end
