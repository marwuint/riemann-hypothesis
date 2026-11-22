import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLat
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapStab
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop
import Formalism.SharpRestriction.InertJacobiLevels.ExtraRec

noncomputable section

namespace Formalism.MainNotions.Gaps.CC.Idx

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.UG.P Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.Gaps.LG
open scoped TensorProduct

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

def adG (σ : E →ₐ[F] E) (J : Matrix n n E)
    (W : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL n (E ⊗[F] v.adicCompletion F))) :
    Subgroup (GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :=
  UPts σ J (FiniteAdeleRing (𝓞 F) F) ⊓ ⨅ v : HeightOneSpectrum (𝓞 F), (W v).comap (bc (prV (E := E) v))

def congU (σ : E →ₐ[F] E) (J : Matrix n n E) (v : HeightOneSpectrum (𝓞 F)) (s : SplitCore σ v)
    (Hk : Subgroup (GL n (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)))) :
    Subgroup (GL n (E ⊗[F] v.adicCompletion F)) :=
  UPts σ J (v.adicCompletion F) ⊓
    (congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) Hk).comap
        (bc ((RingHom.fst _ _).comp s.φ.toRingHom))

end Defs

section SA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem inverse_in_adic_integers (c : 𝓞 F) (w : HeightOneSpectrum (𝓞 F)) [Decidable (Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) < 1)] :
    (if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) < 1 then (0 : w.adicCompletion F)
      else (algebraMap (𝓞 F) (w.adicCompletion F) c)⁻¹) ∈ w.adicCompletionIntegers F := by
  split_ifs with h
  · exact zero_mem _
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
    have h1 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) = 1 :=
      le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (levelaf_int_mem_v w c)) (not_lt.1 h)
    rw [h1, inv_one]

open Classical in

def a_u (c : 𝓞 F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun w => if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) < 1 then (0 : w.adicCompletion F)
      else (algebraMap (𝓞 F) (w.adicCompletion F) c)⁻¹, Filter.Eventually.of_forall fun w => inverse_in_adic_integers c w⟩

theorem a_u_mem (c : 𝓞 F) : a_u c ∈ intAd F := fun w => inverse_in_adic_integers c w

theorem mem_S_of_loc (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) (h : ∀ w, prV (E := E) w x ∈ intV E w) :
    x ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
  classical
  obtain ⟨c, hc0, hc⟩ := loc_int_bound F E
  have hfin := levelaf_finite_places c hc0
  have key : x = ∑ v ∈ hfin.toFinset, afsplitIE v (prV (E := E) v x) +
      ((1 : E) ⊗ₜ[F] a_u c) * (levelafC E c * x) := by
    rw [← sub_eq_zero]
    apply afsplit_inj
    intro w
    rw [map_sub, map_add, map_sum, map_mul, map_mul, sub_eq_zero, afsplit_prV_tmul]
    unfold levelafC
    rw [afsplit_prV_tmul]
    by_cases hw : w ∈ hfin.toFinset
    · rw [Finset.sum_eq_single w (fun v _ hv => afsplit_prV_IE_ne v w (Ne.symm hv) _)
        (fun h => absurd hw h), afsplit_prV_IE]
      have h0 : (a_u c) w = 0 := if_pos (by simpa using hw)
      rw [h0, TensorProduct.tmul_zero, zero_mul, add_zero]
    · rw [Finset.sum_eq_zero (fun v hv => afsplit_prV_IE_ne v w (by rintro rfl; exact hw hv) _), zero_add]
      have h0 : (a_u c) w = (algebraMap (𝓞 F) (w.adicCompletion F) c)⁻¹ := if_neg (by simpa using hw)
      rw [h0, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        show (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) c) w = algebraMap (𝓞 F) (w.adicCompletion F) c from rfl,
        inv_mul_cancel₀ (levelaf_algebraMap_ne_zero w c hc0), ← Algebra.TensorProduct.one_def, one_mul]
  rw [key]
  refine add_mem (Subring.sum_mem _ fun v _ => afsplit_IE_int v _ (h v)) (mul_mem ?_ (hc x h))
  exact Subring.subset_closure (Or.inr ⟨⟨a_u c, a_u_mem c⟩, rfl⟩)

end SA

section TConc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem t_unit_inv {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (τ : A →+* A) (g : GL n A)
    (hg : g ∈ UJ τ (1 : Matrix n n A)) (i j : n) : ((g⁻¹ : GL n A) : Matrix n n A) i j = τ ((g : Matrix n n A) j i) := by
  have h : cT τ (g : Matrix n n A) * 1 * (g : Matrix n n A) = 1 := hg
  rw [Matrix.mul_one] at h
  have h2 : ((g⁻¹ : GL n A) : Matrix n n A) = cT τ (g : Matrix n n A) := by
    calc ((g⁻¹ : GL n A) : Matrix n n A) = (cT τ (g : Matrix n n A) * (g : Matrix n n A)) * ((g⁻¹ : GL n A) : Matrix n n A) := by
          rw [h, Matrix.one_mul]
      _ = cT τ (g : Matrix n n A) := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [h2]
  rfl

variable {k : ℕ} (P : Par F E k)

end TConc

section Asm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {k : ℕ} (P : Par F E k)

variable {P} {f : ℕ}

end Asm

end Formalism.MainNotions.Gaps.CC.Idx

end
