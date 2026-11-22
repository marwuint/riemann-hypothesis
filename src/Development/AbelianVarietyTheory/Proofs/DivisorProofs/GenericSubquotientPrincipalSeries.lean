import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
open NumberField IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspDetBlocks

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.Whittaker

open GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic in

theorem exists_isGeneric_subrep {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (P : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (S : Subrepresentation (P.locRep w)) (hS : S.toSubmodule ≠ ⊥) :
    ∃ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ ∧ ψ ≠ 1 ∧ IsGeneric ψ S.toRepresentation := by
  obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.CuspGeneric.exists_stdPsi E
  have hg : ∀ v : P.V, Good ψ (a - 1) v.1.1 := fun v => _root_.GlobalTheory.CuspGeneric.good_of_isCuspForm E a ψ v.1 (P.cusp _ v.2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨v₀, hv₀S, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hv1 : v₀.1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := _root_.GlobalTheory.CuspGeneric.exists_split_loc E a w g₀
  have hrt : ∀ u (v : P.V) x, whit ψ (a - 1) (P.locRep w u v).1.1 x =
      whit ψ (a - 1) v.1.1 (x * finGL E a (locGL E a w u)) := fun u v x => whit_rt _ _ _ _
  let l : P.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) v.1.1 h
      map_add' := fun v v' => congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => congrFun (whit_smul (a - 1) c v.1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) v.1.1 h := fun _ => rfl
  have hne : l (P.locRep w gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hlaw : ∀ u ∈ unipB (w.adicCompletion E) (Fin a), ∀ v : P.V,
      l (P.locRep w u v) = (locPsi hψ w (superDiag u) : ℂ) * l v := fun u hu v => by
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
    obtain ⟨t1, t2, t3⟩ := _root_.GlobalTheory.CuspRep.locTri_adelic E a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3, superDiag_eq_sum_pairs]
    rfl
  have hcont : Continuous (locPsi hψ w) := by
    refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp
      (CuspSub.continuous_sLoc w)
  have hne1 : locPsi hψ w ≠ 1 := fun h1 => by
    obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  refine ⟨locPsi hψ w, hcont, hne1, l ∘ₗ S.toSubmodule.subtype, fun e' => hne ?_, fun u hu v => ?_⟩
  · exact LinearMap.congr_fun e' ⟨_, S.apply_mem_toSubmodule gw hv₀S⟩
  · exact hlaw u hu v.1

end GlobalTheory.CuspDetBlocks

namespace GlobalTheory.CuspDetBlocks

end GlobalTheory.CuspDetBlocks
