import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open ReciprocityTheory.ChartRestriction.G.PullbackSections (IsEigV)

namespace GlobalTheory.FlagEmb.EigSpread

section Alg

theorem existsUnique_iff {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] (v : ι → M) :
    (∀ w, ∃! a : ι → R, ∑ j, a j • v j = w) ↔ LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination, span_range_eq_top_iff_surjective_fintypeLinearCombination]
  exact (Function.bijective_iff_existsUnique (Fintype.linearCombination R v)).symm

variable {K O ι : Type} [Field K] [CommRing O] [Fintype ι] (χ : ι → O →+* K)

def Splits : Prop :=
  ∀ (S M : Type) [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M] (ρ : O →+* Module.End S M),
    (∀ m, ∃ mm : ι → M, (∀ τ, IsEigV ρ (χ τ) (mm τ)) ∧ ∑ τ, mm τ = m) ∧
    ∀ mm mm' : ι → M, (∀ τ, IsEigV ρ (χ τ) (mm τ)) → (∀ τ, IsEigV ρ (χ τ) (mm' τ)) → ∑ τ, mm τ = ∑ τ, mm' τ → mm = mm'

variable {χ} {R M : Type} [CommRing R] [Algebra K R] [AddCommGroup M] [Module R M] {ρ : O →+* Module.End R M}

omit [Fintype ι] in
theorem eig_single [DecidableEq ι] {τ : ι} {w : M} (hw : IsEigV ρ (χ τ) w) (τ' : ι) :
    IsEigV ρ (χ τ') (Pi.single (M := fun _ => M) τ w τ') := by
  by_cases h : τ' = τ
  · subst h; rwa [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h]; intro a; simp

theorem eig_comb {κ : Type} [Fintype κ] {ψ : O →+* K} {u : κ → M} (hu : ∀ i, IsEigV ρ ψ (u i)) (a : κ → R) :
    IsEigV ρ ψ (∑ i, a i • u i) := fun o => by
  rw [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hu, smul_comm]

theorem block_basis (hs : Splits χ) {m : ι → ℕ} (u : (Σ τ, Fin (m τ)) → M) (hu : ∀ z, IsEigV ρ (χ z.1) (u z))
    (hb : ∀ w, ∃! a : (Σ τ, Fin (m τ)) → R, ∑ z, a z • u z = w) (τ : ι) (w : M) (hw : IsEigV ρ (χ τ) w) :
    ∃! a : Fin (m τ) → R, ∑ i, a i • u ⟨τ, i⟩ = w := by
  classical
  obtain ⟨a, ha, -⟩ := hb w
  have e := (hs R M ρ).2 (fun τ' => ∑ i, a ⟨τ', i⟩ • u ⟨τ', i⟩) (Pi.single τ w)
    (fun τ' => eig_comb (fun i => hu ⟨τ', i⟩) _) (eig_single hw)
    (by rw [Finset.sum_pi_single', if_pos (Finset.mem_univ _), ← ha, Fintype.sum_sigma])
  have e' := congrFun e τ
  rw [Pi.single_eq_same] at e'
  refine ⟨_, e', fun b hb' => ?_⟩
  have li : LinearIndependent R fun i => u ⟨τ, i⟩ :=
    ((existsUnique_iff u).1 hb).1.comp (Sigma.mk τ) sigma_mk_injective
  exact linearIndependent_iff_injective_fintypeLinearCombination.1 li (hb'.trans e'.symm)

theorem global_basis (hs : Splits χ) {m : ι → ℕ} (u : (Σ τ, Fin (m τ)) → M) (hu : ∀ z, IsEigV ρ (χ z.1) (u z))
    (hb : ∀ τ w, IsEigV ρ (χ τ) w → ∃! a : Fin (m τ) → R, ∑ i, a i • u ⟨τ, i⟩ = w) (w : M) :
    ∃! a : (Σ τ, Fin (m τ)) → R, ∑ z, a z • u z = w := by
  obtain ⟨mm, h1, h2⟩ := (hs R M ρ).1 w
  choose c hc hc' using fun τ => hb τ _ (h1 τ)
  refine ⟨fun z => c z.1 z.2, ?_, fun a ha => ?_⟩
  · show ∑ z : Σ τ, Fin (m τ), c z.1 z.2 • u z = w
    rw [Fintype.sum_sigma, ← h2]
    exact Finset.sum_congr rfl fun τ _ => hc τ
  · have e := (hs R M ρ).2 (fun τ' => ∑ i, a ⟨τ', i⟩ • u ⟨τ', i⟩) mm
      (fun τ' => eig_comb (fun i => hu ⟨τ', i⟩) _) h1 (by rw [h2, ← ha, Fintype.sum_sigma])
    funext z
    exact congrFun (hc' z.1 (fun i => a ⟨z.1, i⟩) (congrFun e z.1)) z.2

variable {S N : Type} [CommRing S] [Algebra K S] [AddCommGroup N] [Module S N] {ρ' : O →+* Module.End S N}
  {φ : R →+* S} (f : M →ₛₗ[φ] N)

end Alg

section Geo

open GlobalTheory.FrameTangent MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X} {x' : Sp S ⟶ X}

theorem splits {l : Level H} (c : Coeff l) : Splits (embK c) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c)
    (fun τ a => embK_coe c τ a)
  intro S M _ _ _ _ ρ
  refine ⟨fun m => ⟨fun τ => ReciprocityTheory.ChartRestriction.G.PullbackSections.proj ρ (embK c) α τ m, fun τ =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha _ _ α hN τ (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_eig_alpha _ _ α hinj f hf hfs τ m), ?_⟩,
    fun mm mm' h h' e => funext fun τ => ?_⟩
  · rw [← LinearMap.sum_apply, ReciprocityTheory.ChartRestriction.G.PullbackSections.sum_proj ρ _ α hinj]
    rfl
  · rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ _ α hinj mm h, e, ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ _ α hinj mm' h']

def lf (m : TanM x t.G) : Tn t R := (tv m).left

theorem lf_inj {m m' : TanM x t.G} (h : lf m = lf m') : m = m' := tv_injective (Over.OverMorphism.ext h)

theorem exists_lf {w : Tn t R} (hw : IsTanAtG t x w) : ∃ m : TanM x t.G, lf m = w :=
  ⟨mkT (FrameTangent.ovT (t := t) hw) (FrameTangent.smT_zero_ovT hw), rfl⟩

theorem comb_lf {n : ℕ} (v : Fin n → TanM x t.G) (a : Fin n → R) (w : TanM x t.G) :
    IsCombAtG t x (fun j => lf (v j)) a (lf w) ↔ ∑ j, a j • v j = w := by
  refine (FrameTangent.isCombAtG_iff t x (fun j => tv (v j)) a (lf w)).trans ⟨fun h => lf_inj ?_, fun h => ?_⟩
  · rw [lf, tv_comb]
    exact h
  · rw [← h, lf, tv_comb]
    rfl

def dl (φ : R →+* S) (h : spMap φ ≫ x = x') : tEpsG x' ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
  show spMap (dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) ≫ x = spMap (algebraMap S (DualNumber S)) ≫ x'
  rw [← h, ← Category.assoc, ← Category.assoc, FrameTangent.spMap_comp', FrameTangent.spMap_comp', ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp_alg])

theorem dl_smT (φ : R →+* S) (h : spMap φ ≫ x = x') (a : R) (w : tEpsG x ⟶ t.G) :
    dl φ h ≫ FrameTangent.smT x a w = FrameTangent.smT x' (φ a) (dl φ h ≫ w) := by
  apply Over.OverMorphism.ext
  show spMap (dualMap φ) ≫ spMap (epsMul a) ≫ w.left = spMap (epsMul (φ a)) ≫ spMap (dualMap φ) ≫ w.left
  rw [← Category.assoc, ← Category.assoc, FrameTangent.spMap_comp', FrameTangent.spMap_comp', ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp_epsMul]

variable (t) in

def bcT (φ : R →+* S) (h : spMap φ ≫ x = x') : TanM x t.G →ₛₗ[φ] TanM x' t.G where
  toFun m := mkT (dl φ h ≫ tv m) (by
    rw [← map_zero φ]
    exact (dl_smT φ h 0 (tv m)).symm.trans ((congrArg (dl φ h ≫ ·) (tv_zero' m)).trans (MonObj.comp_one _)))
  map_add' m m' := tv_injective (MonObj.comp_mul (dl φ h) (tv m) (tv m'))
  map_smul' a m := tv_injective (dl_smT φ h a (tv m))

variable {Dw : Datum H} {l : Level H} {c : Coeff l}

end Geo

end GlobalTheory.FlagEmb.EigSpread
