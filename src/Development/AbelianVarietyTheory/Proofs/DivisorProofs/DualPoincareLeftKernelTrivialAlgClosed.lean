import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianVarietyFiniteSubgroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleKernelFiniteSubgroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubgroupSchemePoincareLeftKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfLineBundleOfDualPairLeftTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionFiniteSurjectiveAbelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleDescendsQuotientFiniteSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyTrivialOfQuotientPullbackTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialAdditiveFamilyKilledByIsogeny
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualKer

theorem finite_of_factor {K : Type} [Field K] {N A H : Over (Sp K)} (i : N ⟶ A) (j : H ⟶ A) (z : N ⟶ H)
    (hz : z ≫ j = i) (hi : IsClosedImmersion i.left) (hj : IsClosedImmersion j.left) (hH : IsFinite H.hom) :
    IsFinite N.hom := by
  have e : z.left ≫ j.left = i.left := by rw [← Over.comp_left, hz]
  haveI : IsClosedImmersion (z.left ≫ j.left) := e ▸ hi
  haveI : IsClosedImmersion z.left := IsClosedImmersion.of_comp z.left j.left
  have : N.hom = z.left ≫ H.hom := (Over.w z).symm
  rw [this]; infer_instance

theorem leftKer_eq_one : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → x = 1 := by
  intro K _ _ A B _ _ g P hA hB hgA hgB hP T x hx
  obtain ⟨N, _, i, hi, hci, hNt, hfac⟩ := _root_.GlobalTheory.DualKernel.exists_closed_subgroup_ker K A B P hA hB hP
  obtain ⟨L, H, _, j, hL, -, -, -, hcj, hH, hKL⟩ := _root_.GlobalTheory.KernelSubgroup.exists_finite_subgroup_kernel K A hA
  obtain ⟨z, hz⟩ := (hKL N i).1 (_root_.GlobalTheory.AbDual.memKL_of_triv_ev_left K A B P L hA hB hP hL N i hNt)
  have hfin : IsFinite N.hom := finite_of_factor i j z hz hci hcj hH
  haveI : Mono i.left := inferInstance
  have hmono : Mono i := (Over.forget _).mono_of_mono_map (by simpa using (inferInstance : Mono i.left))
  obtain ⟨A', _, hA', q, hq, hqf, hqfl, hqs, hpb⟩ := _root_.GlobalTheory.AbelianQuotientField.exists_quotient K A hA N i hi hmono hfin
  have hgA' := _root_.GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective K A A' g q hA hA' hqf hqs hgA
  obtain ⟨P', hP', hP'a, hP'i⟩ := _root_.GlobalTheory.PoincareDescent.descends K A A' B N P i q hA hA' hB hP hi hq hqf hqfl hqs hpb hNt
  have hi1 : i = 1 := by
    by_contra hne
    obtain ⟨T', M, hM, hMa, hMq, hMn⟩ := _root_.GlobalTheory.CharKer.exists_nontriv_family K A A' N i q hA hA' hi hq hfin hqf hqfl hqs hpb hne
    exact hMn (_root_.GlobalTheory.DualInjPull.triv_of_triv_pull K A A' B g P P' q hA hA' hB hgA' hgB hP hq hP' hP'a hP'i T' M hM hMa hMq)
  obtain ⟨w, rfl⟩ := hfac T x hx
  rw [hi1, MonObj.comp_one]

end GlobalTheory.DualKer
