import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixModel.Check

open GlobalTheory.OrientedHeis HypDec

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem symplOH_add_self (S T : HSp D) (x y : WO S T) : symplOH S T x y + symplOH S T x y = symplO S T x y := by
  rw [symplOH, ← add_mul, ← map_add, add_halves, map_one, one_mul]

section Source

variable {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ))

theorem mixS_eq (f : WO S T → ℂ) (x : Mx D T.rank ρ) (w₀ : WO S₀ T) : d.mixS T ψ μ 𝓕 f x w₀ =
    ∫ a in 𝓕, ψ (symplOH S T (d.extY T a) (d.extX T x)) * f (d.extY T a + d.extX T x + d.ext0 T w₀) ∂μ := by
  simp only [mixS, integrandS_eq]

theorem mixS_heis_extX (f : WO S T → ℂ) (u x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T u) f) x = d.mixS T ψ μ 𝓕 f (x + u) := by
  funext w₀
  have h : symplOH S T (d.ext0 T w₀) (d.extX T u) = 0 := by rw [symplOH_skew, wittDecomp_sympl_extIsotropic_extAnisotropic, neg_zero]
  simp only [mixS_eq, heisO, map_add (d.extX T), symplOH_add_left, symplOH_add_right, symplOH_extX_extX, h, add_zero,
    AddChar.map_add_eq_mul, mul_assoc]
  congr 1; funext a; congr 3; abel

theorem mixedModelSource_heisenberg_anisotropic_part (f : WO S T → ℂ) (u : WO S₀ T) (x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 (heisO ψ S T (d.ext0 T u) f) x = heisO ψ S₀ T u (d.mixS T ψ μ 𝓕 f x) := by
  funext w₀
  simp only [mixS_eq, heisO, map_add (d.ext0 T), symplOH_add_left, wittDecomp_sympl_extIsotropic_extAnisotropic, wittDecomp_sympl_extDual_extAnisotropic,
    wittDecomp_sympl_extAnisotropic_extAnisotropic, zero_add, ← integral_const_mul, add_assoc]
  congr 1; funext a; ring

variable {μ 𝓕}

theorem mixS_heis_extY (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (y x : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extY T y) f) x w₀ =
      ψ (symplO S T (d.extX T x) (d.extY T y)) * d.mixS T ψ μ 𝓕 f x w₀ := by
  have h : symplOH S T (d.ext0 T w₀) (d.extY T y) = 0 := by rw [symplOH_skew, wittDecomp_sympl_extDual_extAnisotropic, neg_zero]
  have h2 := covolOne_integral_add hμ
    (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0)
    (d.integrandS_periodic hf x w₀) y
  rw [mixS, mixS, ← h2, ← integral_const_mul]
  congr 1; funext a
  simp only [integrandS_eq]
  simp only [heisO, map_add (d.extY T), symplOH_add_left, symplOH_extY_extY, h, add_zero, zero_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, ← symplOH_add_self, symplOH_skew S T (d.extX T x) (d.extY T y)]
  congr 2
  · abel
  · abel

theorem mixS_quasi (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (x : Mx D T.rank ρ) (γ : Matrix (Fin T.rank) (Fin S₀.rank) D.host.E) (w₀ : WO S₀ T) :
    d.mixS T ψ μ 𝓕 f x (ratW T S₀ γ + w₀) = ψ (-(symplOH S₀ T (ratW T S₀ γ) w₀)) * d.mixS T ψ μ 𝓕 f x w₀ := by
  obtain ⟨δ, hδ⟩ : d.ext0 T (ratW T S₀ γ) ∈ ratMx D _ _ := ratMx_mul (rat_mem γ) (rat_mem _)
  simp only [mixS_eq, ← integral_const_mul]
  congr 1; funext a
  have h := hf.quasi δ (d.extY T a + d.extX T x + d.ext0 T w₀)
  rw [show ratW T S δ = d.ext0 T (ratW T S₀ γ) from hδ] at h
  have h1 : symplOH S T (d.ext0 T (ratW T S₀ γ)) (d.extY T a) = 0 := by rw [symplOH_skew, wittDecomp_sympl_extDual_extAnisotropic, neg_zero]
  have h2 : symplOH S T (d.ext0 T (ratW T S₀ γ)) (d.extX T x) = 0 := by rw [symplOH_skew, wittDecomp_sympl_extIsotropic_extAnisotropic, neg_zero]
  rw [symplOH_add_right, symplOH_add_right, h1, h2, wittDecomp_sympl_extAnisotropic_extAnisotropic, zero_add, zero_add] at h
  rw [map_add (d.ext0 T), show d.extY T a + d.extX T x + (d.ext0 T (ratW T S₀ γ) + d.ext0 T w₀) =
    d.ext0 T (ratW T S₀ γ) + (d.extY T a + d.extX T x + d.ext0 T w₀) by abel, h]
  ring

end Source

section Target

variable {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank))

theorem mixT_eq (f : WO S T → ℂ) (y : Mx D S.rank ρ) (w₀ : WO S T₀) : d.mixT S ψ μ 𝓕 f y w₀ =
    ∫ a in 𝓕, ψ (symplOH S T (d.incX S a) (d.incAdj S y)) * f (d.incX S a + d.incAdj S y + d.inc0 S w₀) ∂μ := by
  simp only [mixT, integrandT_eq]

theorem mixT_heis_incAdj (f : WO S T → ℂ) (u y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (heisO ψ S T (d.incAdj S u) f) y = d.mixT S ψ μ 𝓕 f (y + u) := by
  funext w₀
  have h : symplOH S T (d.inc0 S w₀) (d.incAdj S u) = 0 := by
    rw [symplOH_skew, incAdj_apply, wittDecomp_sympl_inclDual_inclAnisotropic, neg_zero]
  have h' : symplOH S T (d.incAdj S y) (d.incAdj S u) = 0 := d.symplOH_incY_incY S _ _
  simp only [mixT_eq, heisO, map_add (d.incAdj S), symplOH_add_left, symplOH_add_right, h, h', add_zero,
    AddChar.map_add_eq_mul, mul_assoc]
  congr 1; funext a; congr 3; abel

theorem mixedModelTarget_heisenberg_anisotropic_part (f : WO S T → ℂ) (u : WO S T₀) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (heisO ψ S T (d.inc0 S u) f) y = heisO ψ S T₀ u (d.mixT S ψ μ 𝓕 f y) := by
  funext w₀
  have h' : symplOH S T (d.incAdj S y) (d.inc0 S u) = 0 := d.wittDecomp_sympl_inclDual_inclAnisotropic S _ _
  simp only [mixT_eq, heisO, map_add (d.inc0 S), symplOH_add_left, wittDecomp_sympl_inclIsotropic_inclAnisotropic, h',
    wittDecomp_sympl_inclAnisotropic_inclAnisotropic, zero_add, ← integral_const_mul, add_assoc]
  congr 1; funext a; ring

variable {μ 𝓕}

end Target

end GlobalTheory.MixModel.Check

end
