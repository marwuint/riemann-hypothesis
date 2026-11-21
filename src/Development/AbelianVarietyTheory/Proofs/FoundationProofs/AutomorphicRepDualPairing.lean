import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducibleEquivariantProjection
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteUnitaryFinitePointsExistsOpenCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalVectorValuedDefiniteUnitaryForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAutRepUSpanValues
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.FrameAut.VecProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {S : Type} [AddCommGroup S] [Module ℂ S]

def forms (ρ : Representation ℂ (infU E n) S) : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {f | (∀ v, f v ∈ autU E n) ∧ ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)}
  add_mem' ha hb := ⟨fun v => add_mem (ha.1 v) (hb.1 v), fun x v => by
    rw [LinearMap.add_apply, LinearMap.add_apply, ha.2, hb.2, map_add]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ ha := ⟨fun v => Submodule.smul_mem _ c (ha.1 v), fun x v => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, ha.2, map_smul]⟩

variable (E n S) in

def post : Representation ℂ (finU E n) (S →ₗ[ℂ] (UA E n → ℂ)) where
  toFun k := LinearMap.llcomp ℂ _ _ _ (RU E n k)
  map_one' := LinearMap.ext fun f => LinearMap.ext fun v => funext fun g => congrArg (f v) (mul_one g)
  map_mul' a b := LinearMap.ext fun f => LinearMap.ext fun v => funext fun g => congrArg (f v) (mul_assoc g a b).symm

@[simp] theorem post_apply (k : finU E n) (f : S →ₗ[ℂ] (UA E n → ℂ)) (v : S) :
    post E n S k f v = RU E n k (f v) := rfl

theorem post_mem (ρ : Representation ℂ (infU E n) S) (k : finU E n) (f : S →ₗ[ℂ] (UA E n → ℂ))
    (h : f ∈ forms ρ) : post E n S k f ∈ forms ρ :=
  ⟨fun v => RU_mem_autU _ _ (h.1 v), fun x v => by
    rw [post_apply, post_apply, h.2, RU_RU, RU_RU, fin_mul_inf k.2 x.2]⟩

def rep (ρ : Representation ℂ (infU E n) S) : Representation ℂ (finU E n) (forms ρ) :=
  GlobalTheory.PRep.sub (post E n S) (forms ρ) (post_mem ρ)

@[simp] theorem rep_val (ρ : Representation ℂ (infU E n) S) (k : finU E n) (f : forms ρ) :
    (rep ρ k f).1 = post E n S k f.1 := rfl

end GlobalTheory.FrameAut.VecProj

namespace GlobalTheory.FrameAut.VecProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {S : Type} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]

def ev (ρ : Representation ℂ (infU E n) S) (v : S) : forms ρ →ₗ[ℂ] autU E n where
  toFun f := ⟨f.1 v, f.2.1 v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def form (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (ρ : Representation ℂ (infU E n) S) :
    forms ρ →ₗ⋆[ℂ] forms ρ →ₗ[ℂ] ℂ :=
  ∑ i, (B.comp (ev ρ (Module.finBasis ℂ S i))).compl₂ (ev ρ (Module.finBasis ℂ S i))

theorem form_apply (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (ρ : Representation ℂ (infU E n) S) (f g : forms ρ) :
    form B ρ f g = ∑ i, B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) g) := by
  simp [form, LinearMap.sum_apply]

end GlobalTheory.FrameAut.VecProj

namespace GlobalTheory.FrameAut.VecProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {S : Type} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]

theorem form_herm (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u)
    (ρ : Representation ℂ (infU E n) S) (f g : forms ρ) : star (form B ρ f g) = form B ρ g f := by
  rw [form_apply, form_apply, star_sum]
  exact Finset.sum_congr rfl fun i _ => hh _ _

theorem form_nonneg (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hp : ∀ v, 0 ≤ (B v v).re)
    (ρ : Representation ℂ (infU E n) S) (f : forms ρ) : 0 ≤ (form B ρ f f).re := by
  rw [form_apply, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => hp _

theorem form_def (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u)
    (hp : ∀ v, 0 ≤ (B v v).re) (hd : ∀ v, B v v = 0 → v = 0)
    (ρ : Representation ℂ (infU E n) S) (f : forms ρ) (h0 : form B ρ f f = 0) : f = 0 := by
  rw [form_apply] at h0
  have hre : ∑ i, (B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f)).re = 0 := by
    rw [← Complex.re_sum, h0, Complex.zero_re]
  have hz : ∀ i, B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f) = 0 := by
    intro i
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp _)).1 hre i (Finset.mem_univ i)
    have h2 : (B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f)).im = 0 := by
      have := congrArg Complex.im (hh (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f))
      rw [Complex.star_def, Complex.conj_im] at this
      linarith
    exact Complex.ext h1 h2
  apply Subtype.ext
  refine (Module.finBasis ℂ S).ext fun i => ?_
  have := congrArg Subtype.val (hd _ (hz i))
  simpa [ev] using this

theorem form_inv (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ)
    (hi : ∀ g u v, B (autRep E n g u) (autRep E n g v) = B u v)
    (ρ : Representation ℂ (infU E n) S) (k : finU E n) (f g : forms ρ) :
    form B ρ (rep ρ k f) (rep ρ k g) = form B ρ f g := by
  rw [form_apply, form_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hi (k : UA E n) (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) g)

theorem rep_smooth (ρ : Representation ℂ (infU E n) S) (f : forms ρ) :
    IsOpen {k : finU E n | rep ρ k f = f} := by
  let b := Module.finBasis ℂ S
  convert isOpen_iInter_of_finite fun i => (f.2.1 (b i)).level using 1
  ext k
  rw [Set.mem_iInter]
  exact ⟨fun h i => LinearMap.congr_fun (congrArg Subtype.val h) (b i), fun h => Subtype.ext (b.ext h)⟩

theorem rep_fd (ρ : Representation ℂ (infU E n) S) (K : Subgroup (finU E n)) (hK : IsOpen (K : Set (finU E n))) :
    FiniteDimensional ℂ (GlobalTheory.PRep.fixed (rep ρ) K) := by
  have hM := _root_.GlobalTheory.DefU.finiteDimensional_vecForms E n S ρ K hK ((GlobalTheory.PRep.fixed (rep ρ) K).map (forms ρ).subtype) (by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨fun v γ hγ x => (g.2.1 v).left γ hγ x, g.2.2, fun k hk v => ?_⟩
    have h1 : rep ρ k g = g := by
      have := hg ⟨k, hk⟩
      rw [MonoidHom.one_apply, Units.val_one, one_smul] at this
      exact this
    exact LinearMap.congr_fun (congrArg Subtype.val h1) v)
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (forms ρ).injective_subtype _).symm

end GlobalTheory.FrameAut.VecProj

namespace GlobalTheory.FrameAut.VecProj

end GlobalTheory.FrameAut.VecProj

end
