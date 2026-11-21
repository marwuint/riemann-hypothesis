import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StdSmoothMvPolynomial
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GaExp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieInh

def ev {A : Type} [CommRing A] {T : Scheme.{0}} (x : Sp A ⟶ T) : Γ(T, ⊤) →+* A :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

private theorem ev_eps_eq_ev {T : Scheme.{0}} (x : Sp (DualNumber ℂ) ⟶ T) (h) (f : Γ(T, ⊤)) :
    GlobalTheory.FibreDeriv.evEps x ⊤ h f = ev x f := by
  have hx : x.appLE ⊤ ⊤ h = x.app ⊤ := by
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  simp only [GlobalTheory.FibreDeriv.evEps, ev, hx]

theorem valAt'_top {T : Scheme.{0}} (x : Sp ℂ ⟶ T) (f : Γ(T, ⊤)) : valAt' x ⊤ f = ev x f := by
  have hx : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x) = x := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext z
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have h1 := GlobalTheory.FibreDeriv.fst_evEps (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x) x hx ⊤ le_rfl f
  rw [← h1, ev_eps_eq_ev]
  have key : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom =
      (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, Category.assoc]
  have h2 := congrArg (fun g => (g.hom f).fst) key
  simpa [ev, TrivSqZeroExt.algebraMap_eq_inl] using h2

variable {R : Type} [CommRing R]

instance : IsAffine (gaObj (Sp R)).left := inferInstanceAs (IsAffine 𝔸(Fin 1; Sp R))

variable {G : Over (Sp R)} [GrpObj G] {g n : ℕ} {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)}
  {ψ : (Fin n → ℂ) → (R →+* ℂ)}

theorem dir_unique (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) {w w' : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ G.left} (h : IsDerivAt0 (fun z => (e.ex b z).left) w v)
    (h' : IsDerivAt0 (fun z => (e.ex b z).left) w' v) : w = w' := by
  obtain ⟨V, N, f, L, hV, hL, hLz, -⟩ := e.log b hb
  rw [GlobalTheory.FibreDeriv.isDerivAt0_iff] at h h'
  have hv : ⊤ ≤ v ⁻¹ᵁ V := (GlobalTheory.FibreDeriv.top_le_preimage_eps v _ h.1 V).2 hV
  have hjet : ∀ j, fderiv ℂ (fun z => valAt' (e.ex b z).left V (f j)) 0 w =
      fderiv ℂ (fun z => valAt' (e.ex b z).left V (f j)) 0 w' := by
    intro j
    have e1 := congrArg TrivSqZeroExt.snd (h.2 V hv (f j))
    have e2 := congrArg TrivSqZeroExt.snd (h'.2 V hv (f j))
    rw [GlobalTheory.FibreDeriv.snd_jet] at e1 e2
    exact e1.symm.trans e2
  have hΦd : DifferentiableAt ℂ (fun z (j : Fin N) => valAt' (e.ex b z).left V (f j)) 0 :=
    differentiableAt_pi.2 fun j => ExpLift.ex_differentiableAt e hb V (f j) hV
  have hΦw : fderiv ℂ (fun z (j : Fin N) => valAt' (e.ex b z).left V (f j)) 0 w =
      fderiv ℂ (fun z (j : Fin N) => valAt' (e.ex b z).left V (f j)) 0 w' := by
    rw [fderiv_pi (fun j => ExpLift.ex_differentiableAt e hb V (f j) hV)]
    funext j
    simp only [ContinuousLinearMap.pi_apply]
    exact hjet j
  have hloc : (fun z => L (b, fun j => valAt' (e.ex b z).left V (f j))) =ᶠ[𝓝 0] id := by
    have ht : Tendsto (fun z : Fin g → ℂ => (b, z)) (𝓝 0) (𝓝 (b, 0)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    exact ht.eventually hLz
  have h1 : HasFDerivAt (fun z => L (b, fun j => valAt' (e.ex b z).left V (f j)))
      (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 :=
    (hasFDerivAt_id (0 : Fin g → ℂ)).congr_of_eventuallyEq hloc
  have h2 := hL.differentiableAt.hasFDerivAt.comp (0 : Fin g → ℂ)
    ((hasFDerivAt_const b (0 : Fin g → ℂ)).prodMk hΦd.hasFDerivAt)
  have h3 := h1.unique h2
  calc w = ContinuousLinearMap.id ℂ (Fin g → ℂ) w := rfl
    _ = _ := congrArg (fun T => T w) h3
    _ = _ := by simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, zero_apply, hΦw]
    _ = ContinuousLinearMap.id ℂ (Fin g → ℂ) w' := (congrArg (fun T => T w') h3).symm
    _ = w' := rfl

end GlobalTheory.CompanionTheory.Ar.Flat.GaExp
