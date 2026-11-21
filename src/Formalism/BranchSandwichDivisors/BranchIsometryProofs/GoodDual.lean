import Formalism.BranchSandwichDivisors.StatementL
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.RatHerm

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.BranchingDeterminantCap

namespace GoodDualLattice

section

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def tw (g : V →ₗ⋆[K] K) : V →ₗ[K] K where
  toFun y := star (g y)
  map_add' a b := by simp
  map_smul' k y := by simp [starRingEnd_apply]

omit [IsDedekindDomain R] [StarRing K] in

theorem denom {ι : Type*} [Fintype ι] (b : Basis ι K V) (v : V) :
    ∃ (d : R) (n : ι → R), d ≠ 0 ∧ d • v = ∑ i, n i • b i := by
  classical
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ
    (fun i => b.repr v i)
  choose a ha using fun i => RingHom.mem_rangeS.mp (hd i (Finset.mem_univ i))
  refine ⟨d, a, nonZeroDivisors.coe_ne_zero d, ?_⟩
  conv_lhs => rw [← b.sum_repr v, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_assoc, ← algebraMap_smul K (a i), ha i]

omit [IsDedekindDomain R] [StarRing K] in

theorem ext_zero {ι : Type*} [Fintype ι] (b : Basis ι K V) (A : Submodule R V) (hb : ∀ i, b i ∈ A)
    (D : A →ₗ[R] K) (hD : ∀ i, D ⟨b i, hb i⟩ = 0) (a : A) : D a = 0 := by
  obtain ⟨d, n, hd, hdn⟩ := denom (R := R) b (a : V)
  have h1 : d • a = ∑ i, n i • (⟨b i, hb i⟩ : A) := by
    apply Subtype.ext
    simp [hdn]
  have h2 : d • D a = 0 := by
    rw [← map_smul, h1, map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smul, hD, smul_zero]
  have hd' : algebraMap R K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd
  rw [Algebra.smul_def] at h2
  exact (mul_eq_zero.mp h2).resolve_left hd'

theorem dual_exists [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hnd : ∀ x, (∀ y, h y x = 0) → x = 0) (e : V →ₗ[K] V) (hee : ∀ x, e (e x) = e x)
    (hsa : ∀ x y, h (e x) y = h x (e y)) (A : Submodule R V) (hfg : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (x : V) (hxe : e x = x)
    (hx : ∀ y ∈ A, e y = y → h y x ∈ (1 : Submodule R K)) :
    ∃ z : V, (∀ y ∈ A, h y z ∈ (1 : Submodule R K)) ∧ e z = x := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have : Module.IsTorsionFree R V := Module.IsTorsionFree.trans_faithfulSMul R K V
  obtain ⟨s0, _, b, hbs, hs0⟩ := Formalism.HermitianLatticesTheory.dualLattice_basis (R := R) A hsp
  have hb : ∀ i, b i ∈ A := fun i => by rw [hbs]; exact hs0 i.2

  let N : Submodule R A := ((LinearMap.range e).restrictScalars R).comap A.subtype
  have hN : ∀ a : A, a ∈ N ↔ e a = a := by
    intro a
    constructor
    · rintro ⟨w, hw⟩
      have hw' : e w = (a : V) := hw
      rw [← hw', hee]
    · intro h
      exact ⟨a, h⟩
  have : Module.IsTorsionFree R (A ⧸ N) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r q hq
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    rw [Submodule.Quotient.mk_eq_zero, hN]
    rw [hN] at hq
    have hq' : r • e (a : V) = r • (a : V) := by
      rw [← LinearMap.map_smul_of_tower]; exact hq
    have hr' : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ hinj).mpr hr
    rw [← algebraMap_smul K r, ← algebraMap_smul K r] at hq'
    exact smul_right_injective V hr' hq'
  have : Module.Finite R A := Module.Finite.iff_fg.mpr hfg
  have : Module.FinitePresentation R (A ⧸ N) := Module.finitePresentation_of_finite R _
  have : Module.Projective R (A ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hsN : ∀ a : A, a - s (N.mkQ a) ∈ N := by
    intro a
    have h := LinearMap.congr_fun hs (N.mkQ a)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
    change N.mkQ a - N.mkQ (s (N.mkQ a)) = 0
    rw [h, sub_self]

  let ψ : A →ₗ[R] K :=
    (tw (h.flip x)).restrictScalars R ∘ₗ A.subtype ∘ₗ (LinearMap.id - s ∘ₗ N.mkQ)
  have hψ : ∀ a : A, ψ a = star (h ((a - s (N.mkQ a) : A) : V) x) := fun a => rfl
  have hψN : ∀ a : A, e a = a → ψ a = star (h (a : V) x) := by
    intro a ha
    have h0 : N.mkQ a = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hN]; exact ha
    rw [hψ, h0, map_zero, sub_zero]

  let L : V →ₗ[K] (s0 → K) :=
    { toFun := fun z i => h (b i) z
      map_add' := fun a c => by ext i; simp
      map_smul' := fun k a => by ext i; simp }
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    apply hnd
    have hz0 : h.flip z = 0 := b.ext fun i => by
      have := congr_fun hz i
      simpa [L] using this
    intro y
    have := LinearMap.congr_fun hz0 y
    simpa using this
  have hLsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis b])).mp hLinj
  obtain ⟨z, hzL⟩ := hLsurj (fun i => star (ψ ⟨b i, hb i⟩))
  have hzb : ∀ i, h (b i) z = star (ψ ⟨b i, hb i⟩) := fun i => congr_fun hzL i
  have hzA : ∀ a : A, star (h (a : V) z) = ψ a := by
    intro a
    have h0 := ext_zero b A hb ((tw (h.flip z)).restrictScalars R ∘ₗ A.subtype - ψ) (fun i => by
      change star (h (b i) z) - ψ ⟨b i, hb i⟩ = 0
      rw [hzb, star_star, sub_self]) a
    exact sub_eq_zero.mp h0
  have hzV : ∀ v : V, e v = v → h v z = h v x := by
    intro v hv
    obtain ⟨d, n, hd, hdn⟩ := denom (R := R) b v
    have hdA : d • v ∈ A := by
      rw [hdn]
      exact A.sum_mem fun i _ => A.smul_mem _ (hb i)
    have hev : e (d • v) = d • v := by rw [LinearMap.map_smul_of_tower, hv]
    have h1 : star (h (d • v) z) = star (h (d • v) x) := by
      rw [hzA ⟨d • v, hdA⟩, hψN ⟨d • v, hdA⟩ hev]
    have h2 := star_injective h1
    have hd' : star (algebraMap R K d) ≠ 0 :=
      star_ne_zero.mpr ((map_ne_zero_iff _ hinj).mpr hd)
    rw [← algebraMap_smul K d v] at h2
    simp only [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul] at h2
    exact mul_left_cancel₀ hd' h2
  refine ⟨z, fun y hy => ?_, ?_⟩
  · have h1 := hzA ⟨y, hy⟩
    rw [hψ] at h1
    rw [show h y z = h (((⟨y, hy⟩ : A) - s (N.mkQ ⟨y, hy⟩) : A) : V) x from star_injective h1]
    exact hx _ (Subtype.mem _) ((hN _).mp (hsN _))
  · have key : ∀ w, h w (e z - x) = 0 := by
      intro w
      rw [map_sub, ← hsa, hzV (e w) (hee w), hsa, hxe, sub_self]
    exact sub_eq_zero.mp (hnd _ key)

end

end GoodDualLattice

end Formalism.BranchingDeterminantCap
