import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPeriodCompIsometry
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOfFinOrderOfQuadratic
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsContraction

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.LevStab

open GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

theorem exists_isometry_of_hol {S : Scheme.{0}} {t : SAB H S} {y : Sp ℂ ⟶ S} {D D' : Datum H} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} {P' : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P')
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (ha : ∀ z w, e (z + w) = e z * e w) (hs : Function.Surjective e)
    (hhol : IsHolTo Set.univ (fun z => (e z).left)) (he' : IsExp e')
    (hr : ReadsPeriods t unitOn D ty P e) (hr' : ReadsPeriods t unitOn D' ty P' e') :
    ∃ (gam : D.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ ∀ z, e' (h z) = e z := by
  obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP' he' hr'.1 ha hs hhol
    ((countable_periods hP).mono fun z hz => (hr.1 z).1 hz)
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have := hP'.2.2.1
    have k := realLinear_eq_of_sub_mem_discrete (Γ := P'.range) DiscreteTopology.isDiscrete
      (L := (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)))
      (L' := LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ)) fun x =>
        (hr'.1 _).1 ((eq_iff_sub_of_add he'.1 _ _).1
          (((hh _).trans (hr.2.1 a x)).trans (by rw [← hh]; exact (hr'.2.1 a (h x)).symm)))
    exact DFunLike.congr_fun k z
  have hmem : ∀ a, ∃ b, P' b = h (P a) := fun a => (hr'.1 _).1 ((hh _).trans ((hr.1 _).2 ⟨a, rfl⟩))
  choose r₀ hr₀ using hmem
  let r₁ : D.La →ₗ[𝓞 E] D'.La :=
    { toFun := r₀
      map_add' := fun a b => hP'.2.1 (by rw [map_add, hr₀, hr₀, hr₀, map_add, map_add])
      map_smul' := fun c a => hP'.2.1 (by
        rw [hr₀, show P (c • a) = fun k => ty k (c : E) * P a k from funext (hP.1 c a), hcomm, ← hr₀]
        exact (funext (hP'.1 c (r₀ a))).symm) }
  have hb : Function.Bijective r₁ := by
    refine ⟨fun a b hab => hP.2.1 (h.injective (((hr₀ a).symm.trans (congrArg P' hab)).trans (hr₀ b))), fun b => ?_⟩
    obtain ⟨a, ha⟩ := (hr.1 (h.symm (P' b))).1 (by rw [← hh, h.apply_symm_apply]; exact (hr'.1 _).2 ⟨b, rfl⟩)
    exact ⟨a, hP'.2.1 ((hr₀ a).trans (by rw [ha, h.apply_symm_apply]))⟩
  refine ⟨LinearEquiv.ofBijective r₁ hb, h, fun a b => int_eq_of_exp_eq fun k hk => ?_, hr₀, hh⟩
  have w := hr.2.2 k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  have w' := hr'.2.2 k (r₀ a) (r₀ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  rw [hr₀, hr₀, ← map_smul h, ← map_smul h, hh, hh] at w'
  exact congrArg Units.val (weilIs_unique_fieldPoint _ _ _ t.PP.isLB ℂ y k _ _ _ _ w' w)

theorem map_mem_smul_top {R L L' : Type*} [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    (I : Ideal R) (f : L →ₗ[R] L') {x : L} (hx : x ∈ I • (⊤ : Submodule R L)) : f x ∈ I • (⊤ : Submodule R L') := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)}

theorem exists_isometry_of_levAut (F : FamilyUnif Xo σ ty) {s : Sim D} {ρ : Xo.X ≅ Xo.X} (hρ : Xo.LevAut s ρ)
    {i j : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} {P' : (F.Di j).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di j) ty P') (hu : F.u i P ≫ ρ.hom = F.u j P') :
    ∃ gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di j).La, (∀ a b, (F.Di j).EF (gam a) (gam b) = (F.Di i).EF a b) ∧
      ∀ a, gam (F.t i (s.f l.M a)) - F.t j a ∈ l.Mb • (⊤ : Submodule (𝓞 E) (F.Di j).La) := by
  obtain ⟨-, ν, hη, -⟩ := hρ
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨β, hβ⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv ν.cart (Over.mk (F.u i P)) (s := F.u j P') hu.symm
  have hr : ReadsPeriods Xo.univ.t unitOn (F.Di i) ty P (fun z => β (F.ex i P z)) := by
    refine ⟨fun z => by rw [β.map_eq_one_iff, F.ex_ker i P hP], fun a z => ?_, fun k a b c hk hc => ?_⟩
    · apply Over.OverMorphism.ext
      rw [hβ, F.ex_lin i P hP, Over.comp_left, Over.comp_left, hβ, Category.assoc, Category.assoc]
      exact congrArg _ (ν.act a)
    · obtain ⟨w, hw, -⟩ := ν.lin
      have h₁ := (weilIs_grpPullback_of_comm _ _ Xo.univ.t.G Xo.univ.t.G ρ.hom ν.φ _ _ Xo.univ.t.PP.isLB
        Xo.univ.t.PP.isLB ν.cart ⟨w, hw⟩ _ k _ _ (pushPt ν.cart.1.w _) (pushPt ν.cart.1.w _) _ rfl rfl).1
        (F.ex_weil i P hP k a b c hk hc)
      exact weilIs_congr hu (hβ _).symm (hβ _).symm h₁
  obtain ⟨gam, h, hEF, hh, hx⟩ := exists_isometry_of_hol hP hP' (e := fun z => β (F.ex i P z)) (e' := F.ex j P')
    (fun z w => by rw [F.ex_add i P hP, map_mul]) (β.surjective.comp (F.ex_onto i P hP))
    (by
      simp only [hβ]
      exact GlobalTheory.CMSpreadCompare.isHolTo_postcomp (GlobalTheory.ClassUniq.isHolTo_ex F i P hP) _)
    ⟨F.ex_add j P' hP', F.ex_onto j P' hP', GlobalTheory.ClassUniq.isHolTo_ex F j P' hP', (F.ex_diff j P' hP').1,
      (F.ex_diff j P' hP').2⟩ hr ⟨F.ex_ker j P' hP', F.ex_lin j P' hP', F.ex_weil j P' hP'⟩
  refine ⟨gam, hEF, fun a => ?_⟩
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
    trivial
  obtain ⟨x, hx₀, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
  have hxm : gam (F.t i (s.f l.M x)) - F.t j x ∈ l.Mb • (⊤ : Submodule (𝓞 E) (F.Di j).La) :=
    Submodule.sub_mem _ (map_mem_smul_top _ gam.toLinearMap (map_mem_smul_top _ _ (map_mem_smul_top _ _ hx₀)))
      (map_mem_smul_top _ _ hx₀)
  have hym : gam (F.t i (s.f l.M y)) - F.t j y ∈ l.Mb • (⊤ : Submodule (𝓞 E) (F.Di j).La) := by
    obtain ⟨v, hv⟩ : ∃ v, gam (F.t i (s.f l.M y)) = F.t j y + l.M • v := by
      refine (div_eq_iff hP'.2.1 (F.ex_add j P' hP') (F.ex_ker j P' hP') hM0 _ _).1 ?_
      rw [hh, ← map_smul h, hx, ← F.ex_eta j P' hP' y hy, ← F.ex_eta i P hP _ (map_mem_smul_top _ _ hy)]
      apply Over.OverMorphism.ext
      rw [hβ]
      change (F.u i P ≫ (Xo.univ.eta (s.f l.M y)).left) ≫ ν.φ = F.u j P' ≫ (Xo.univ.eta y).left
      rw [Category.assoc, hη, ← Category.assoc, hu]
    rw [hv, add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    refine Submodule.smul_mem_smul ?_ trivial
    have hM : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]
      exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf.trans inf_le_left) hM
  have := Submodule.add_mem _ hxm hym
  rwa [sub_add_sub_comm, ← map_add, ← map_add, ← map_add, ← map_add] at this

end GlobalTheory.LevStab

end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

