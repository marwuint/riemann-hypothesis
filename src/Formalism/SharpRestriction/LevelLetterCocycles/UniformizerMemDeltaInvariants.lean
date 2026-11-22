import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.SharpRestriction.LevelLetterCocycles.LengthNeTopOfSmul
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LemmaDN0

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.LD

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.DCount

section Setup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem ndl_smul (i : ZMod n) {a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T} (hx : x ∈ NDl W T i) :
    a • x ∈ NDl W T i := by
  have hx' : x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x := hx
  have hD : (letE i : LetA O n) • x = x ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := hx'.2
  have ha' : ∀ δ ∈ W.DelF, W.γA δ a = a := ha
  show a • x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (a • x)
  refine ⟨(W.N T).smul_mem a hx'.1, ?_, ?_⟩
  · rw [smul_smul, mul_comm, ← smul_smul, hD.1]
  · intro δ hδ
    have hγ : letγ (W.γ₀ δ) a = a := ha' δ hδ
    rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, hD.2 δ hδ, hγ]

theorem qp_mem (hπ : W.π₀ ∈ W.AΔ) : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := by
  show W.π₀ + ((PD.p : ℕ) : LetA O n) ∈ W.AΔ
  exact add_mem hπ (Subalgebra.natCast_mem _ _)

def QhP (i : ZMod n) (h : ℕ) : Submodule O (W.DD T) :=
  (PhiPullΔ W T i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ h) • (LinearMap.id : W.DD T →ₗ[O] W.DD T))

def qN (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) : ↥(NDl W T i) →ₗ[O] ↥(NDl W T i) :=
  (Formalism.MainNotions.LiftingTheory.qp W • (NDl W T i).subtype).codRestrict (NDl W T i)
    (fun x => ndl_smul W T i (qp_mem W hπ) x.2)

private lemma exists_pow_eq_one_mul {Γ : Type} [CommGroup Γ] {a b : Γ} (ha : ∃ k : ℕ, 0 < k ∧ a ^ k = 1)
    (hb : ∃ k : ℕ, 0 < k ∧ b ^ k = 1) : ∃ k : ℕ, 0 < k ∧ (a * b) ^ k = 1 := by
  obtain ⟨k, hk, hak⟩ := ha
  obtain ⟨m, hm, hbm⟩ := hb
  refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
  rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm, pow_mul, hbm, one_pow]

private lemma exists_pow_eq_one_inv {Γ : Type} [CommGroup Γ] {a : Γ} (ha : ∃ k : ℕ, 0 < k ∧ a ^ k = 1) :
    ∃ k : ℕ, 0 < k ∧ a⁻¹ ^ k = 1 := by
  obtain ⟨k, hk, hak⟩ := ha
  exact ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩

theorem uniformizer_mem_delta_invariants : W.π₀ ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀
  intro δ hδ
  have hδt := (W.DelF_def δ).1 hδ
  funext i
  show W.γ₀ δ W.π₀₁ = W.π₀₁
  simp only [Formalism.BasicNotions.LocWach.π₀₁, map_add, map_sub, map_one, map_natCast, map_sum]
  congr 1
  refine Finset.sum_equiv (Equiv.mulLeft δ) ?_ ?_
  · intro g
    simp only [Equiv.coe_mulLeft]
    rw [W.DelF_def g, W.DelF_def (δ * g)]
    constructor
    · exact fun hg => exists_pow_eq_one_mul hδt hg
    · intro hg
      have h2 := exists_pow_eq_one_mul (exists_pow_eq_one_inv hδt) hg
      rwa [inv_mul_cancel_left] at h2
  · intro g _
    simp only [Equiv.coe_mulLeft, map_mul, AlgHom.mul_apply]

end Setup

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def NinQbP [NeZero n] : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → m = 0 → ∀ i ∈ evens n d, ∀ x ∈ NDl W T₂ i,
      x ∈ (PhiPullΔ W T₂ i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂))

end Main

end Formalism.MainNotions.RamifiedCoefficientChains.S9.LD
