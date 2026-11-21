import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVecC
import Formalism.LocalToGlobal.ProjectiveLattices.FrCovA

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocFrame

section Alg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
open GlobalTheory.LieMet (tanOf isTan_tv isTan_map tan_ext)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T U : Type} [CommRing S] [CommRing T] [CommRing U] {x : Sp S ⟶ X} {x' : Sp T ⟶ X} {x'' : Sp U ⟶ X}

def res (ψ : S →+* T) (hx : spMap ψ ≫ x = x') (v : TanM x t.G) : TanM x' t.G := tanOf (isTan_map ψ hx (isTan_tv v))

theorem res_res (ψ : S →+* T) (hx : spMap ψ ≫ x = x') (χ : T →+* U) (hx' : spMap χ ≫ x' = x'') {ω : S →+* U}
    (e : χ.comp ψ = ω) (hx'' : spMap ω ≫ x = x'') (v : TanM x t.G) :
    res χ hx' (res ψ hx v) = res ω hx'' v := by
  subst e
  refine tan_ext ?_
  show spMap (dualMap χ) ≫ spMap (dualMap ψ) ≫ _ = spMap (dualMap (χ.comp ψ)) ≫ _
  rw [← Category.assoc, spMap_comp_spMap]
  congr 2
  exact RingHom.ext fun a => by ext <;> simp [dualMap]

theorem res_sum (ψ : S →+* T) (hx : spMap ψ ≫ x = x') {κ : Type} [Fintype κ] (a : κ → S) (n : κ → TanM x t.G) :
    res ψ hx (∑ k, a k • n k) = ∑ k, ψ (a k) • res ψ hx (n k) := by
  subst hx
  let ρ : overAt (spMap ψ ≫ x) (DualNumber T) ⟶ overAt x (DualNumber S) := Over.homMk (spMap (dualMap ψ)) (by
    show spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap _ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, PullbackSections.dualMap_comp_alg])
  let f : TanM x t.G →+ TanM (spMap ψ ≫ x) t.G :=
    AddMonoidHom.mk' (res ψ rfl) fun a b => tanM_ext (MonObj.comp_mul ρ (tv a) (tv b))
  refine (map_sum f _ _).trans (Finset.sum_congr rfl fun k _ => tan_ext ?_)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (tv (n k)).left) (FrCov.eps_dual ψ (a k))).trans
    (Category.assoc _ _ _))

def IsBasis {m : ℕ} (v : Fin m → TanM x t.G) : Prop := ∀ n : TanM x t.G, ∃! a : Fin m → S, n = ∑ k, a k • v k

theorem isBasis_iff {m : ℕ} {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G x Φ) {u : Fin m → (epsR S ⟶ G')} {v : Fin m → TanM x t.G}
    (e : ∀ i, pushHom h (epsR S) (u i) = tv (v i)) : IsLieBasis u ↔ IsBasis v := by
  have hs : ∀ a : Fin m → S, tv (∑ i, a i • v i) = combT x (fun i => tv (v i)) a := fun a => by
    classical
    unfold combT
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => rfl
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, tv_add, ih]; rfl
  have key : ∀ a p n, pushHom h (epsR S) p = tv n → (IsLieComb a u p ↔ n = ∑ k, a k • v k) := fun a p n hp => by
    rw [isLieComb_iff h, hp]
    simp only [e]
    exact ⟨fun q => tanM_ext (q.trans (hs a).symm), fun q => (congrArg tv q).trans (hs a)⟩
  refine ⟨fun hu n => ?_, fun hv => ⟨fun i => (isTangent_iff h _).2 (by rw [e]; exact tv_mem _), fun p hp => ?_⟩⟩
  · obtain ⟨p, hp⟩ := push_surj h (tv n)
    simpa only [key _ p n hp] using hu.2 p ((isTangent_iff h p).2 (by rw [hp]; exact tv_mem n))
  · simpa only [key _ p (mkT _ ((isTangent_iff h p).1 hp)) rfl] using hv (mkT _ ((isTangent_iff h p).1 hp))

theorem IsBasis.res {m : ℕ} {v : Fin m → TanM x t.G} (hv : IsBasis v) (ψ : S →+* T) (hx : spMap ψ ≫ x = x') :
    IsBasis fun i => res ψ hx (v i) := by
  subst hx
  have h₀ := isGrpPullback_pullback t.G x
  have h := isGrpPullback_pullback t.G (spMap ψ ≫ x)
  choose u hu using fun i => push_surj h₀ (tv (v i))
  choose u' hu' using fun i => push_surj h (tv (LieLocFrame.res ψ rfl (v i)))
  have := t.semi.smooth
  have : Smooth ((Over.pullback x).obj t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  refine (isBasis_iff h hu').1 (Chart.frameLieBCR _ ((isBasis_iff h₀ hu).2 hv) ψ
    (Chart.isGrpPullback_factor x (spMap ψ) h)
    (fun a b v hv => push_inj h (by
      have := smT_add _ _ ((isTangent_iff h v).1 ((Chart.isTan_iff _).1 hv)) a b
      rw [← push_scK h, ← push_scK h, ← push_scK h, ← map_mul] at this
      exact this)) (fun i => (isTangent_iff h _).2 (by rw [hu']; exact tv_mem _)) fun i => ?_)
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc]
    exact (congrArg (fun q => q.left) (hu' i)).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (hu i)).symm)
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (u' i), Category.assoc]
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Over.w (u i)).symm)
    exact (spMap_comp_spMap _ _).trans ((congrArg spMap (PullbackSections.dualMap_comp_alg _).symm).trans (spMap_comp_spMap _ _).symm)

end Alg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

end GlobalTheory.LieLocFrame
