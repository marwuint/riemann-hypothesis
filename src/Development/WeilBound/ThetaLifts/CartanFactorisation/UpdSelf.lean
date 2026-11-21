import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsBeta
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped ComplexConjugate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
  {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

def upd {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x : (κ → Fv F v) → ℂ) : ∀ u : Pl F, (κ → Fv F u) → ℂ := by
  classical exact Function.update φ v x

theorem upd_self {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x) : upd φ v x v = x := by
  classical exact Function.update_self ..

theorem upd_ne {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x) {u} (h : u ≠ v) : upd φ v x u = φ u := by
  classical exact Function.update_of_ne h ..

theorem upd_eq {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) : upd φ v (φ v) = φ := by
  classical exact Function.update_eq_self ..

theorem upd_upd {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x y) : upd (upd φ v x) v y = upd φ v y := by
  classical exact Function.update_idem ..

theorem upd_sb {κ : Type} [Fintype κ] {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ u, φ u ∈ SB _) {v : Pl F} {x} (hx : x ∈ SB _) (u) :
    upd φ v x u ∈ SB _ := by
  by_cases e : u = v
  · subst e; rwa [upd_self]
  · rw [upd_ne _ _ _ e]; exact h u

theorem upd_cof {κ : Type} {φ ψ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = ψ u) (v : Pl F) (x) :
    ∀ᶠ u in cofinite, upd φ v x u = ψ u :=
  (h.and (Filter.eventually_cofinite_ne v)).mono fun _ hu => (upd_ne _ _ _ hu.2).trans hu.1

theorem intersection_update_fsHerm_neg_one (hP : PureAct) (hp : IsPair B M χX χW om r s r' s') (f : SInf F (Fin n × Fin d)) {φ} (h1 : ∀ u, φ u ∈ SB _)
    (h2 : ∀ᶠ u in cofinite, φ u = M.vac u) (v : Pl F) :
    ∃ j : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Fn F n d, (∀ x, j x = pure f (upd φ v x)) ∧
      ∀ S, ∀ x ∈ SB _, ∀ y, Acts (evFin F v) S x y → S (j x) = j y := by
  have h3 := (h2.and hp.good.std).mono fun _ h => h.1.trans h.2
  have l : ∀ x y (a : ℂ), pure f (upd φ v (x + a • y)) = pure f (upd φ v x) + a • pure f (upd φ v y) :=
    (hP F _ v id f φ h1 h3).2.1
  have z : pure f (upd φ v 0) = 0 := by
    have := l 0 0 1
    simp only [one_smul, add_zero] at this
    exact left_eq_add.1 this
  refine ⟨{ toFun := fun x => pure f (upd φ v x)
            map_add' := fun x y => by simpa using l x y 1
            map_smul' := fun c x => by
              have := l 0 x c
              rwa [zero_add, z, zero_add] at this },
    fun _ => rfl, fun S x hx y hxy => ?_⟩
  have := (hP F _ v S f (upd φ v x) (upd_sb h1 hx) (upd_cof h3 v x)).2.2 y (by rwa [upd_self])
  exact this.trans (congrArg (pure f) (upd_upd φ v x y))

end PositivityTheory.ThKF

end
