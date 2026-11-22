import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdmissibleHarmonicLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNeZeroSmulMemOfMemSpan

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenusLatCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped Pointwise

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def toGen (Λ : Lat E n) : GenLat E n := ⟨Λ.L⟩

def IsLat (Λ : GenLat E n) : Prop := Λ.La.FG ∧ Submodule.span E (Λ.La : Set (Fin n → E)) = ⊤

def latEquiv : Lat E n ≃ {Λ : GenLat E n // IsLat Λ} where
  toFun Λ := ⟨toGen Λ, Λ.fg, Λ.span_top⟩
  invFun Λ := ⟨Λ.1.La, Λ.2.1, Λ.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem stdLat_eq : stdLat E n = stdMod E n := rfl

omit [NumberField E] in
theorem span_smul_le_iff (k : ℕ) (A B : Submodule (𝓞 E) (Fin n → E)) :
    Ideal.span {(k : 𝓞 E)} • A ≤ B ↔ ∀ x ∈ A, k • x ∈ B := by
  rw [Submodule.smul_le]
  constructor
  · intro h x hx
    have := h k (Ideal.mem_span_singleton_self _) x hx
    rwa [Nat.cast_smul_eq_nsmul] at this
  · intro h r hr x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
    exact B.smul_mem _ (h x hx)

theorem fg_of_smul_mem {A : Submodule (𝓞 E) (Fin n → E)} {o : 𝓞 E} (ho : o ≠ 0)
    (h : ∀ x ∈ A, o • x ∈ stdMod E n) : A.FG := by
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 E) (Fin n → E) o) := by
    intro x y hxy
    funext j
    have := congrFun hxy j
    simp only [LinearMap.lsmul_apply, Pi.smul_apply, Algebra.smul_def] at this
    exact mul_left_cancel₀ (by simpa using ho) this
  refine Submodule.fg_of_fg_map_injective _ hinj ?_
  haveI : IsNoetherian (𝓞 E) (stdMod E n) := isNoetherian_of_fg_of_noetherian _ (Lat.std E n).fg
  refine Submodule.FG.of_le_of_isNoetherian (T := stdMod E n) ?_
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

variable [IsCMField E]

theorem eq_zero_of_sum_conj (v : Fin n → E) (h : ∑ j, IsCMField.complexConj E (v j) * v j = 0) : v = 0 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := congrArg φ h
  simp only [map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_zero,
    Complex.conj_mul'] at h1
  have h2 : ∑ j, ‖φ (v j)‖ ^ 2 = 0 := by exact_mod_cast h1
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity] at h2
  funext j
  simpa using h2 j (Finset.mem_univ j)

omit [IsCMField E] in

private theorem exists_mul_mem_of_mem_span (A : Submodule (𝓞 E) (Fin n → E)) {x : Fin n → E}
    (hx : x ∈ Submodule.span E (A : Set (Fin n → E))) : ∃ o : 𝓞 E, o ≠ 0 ∧ o • x ∈ A := by
  first
  | exact @_root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span
  | exact _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span
  | (apply _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span ..)

private theorem span_eq_top_of_unimod (Λ : GenLat E n) (h : Λ.Unimod) :
    Submodule.span E (Λ.La : Set (Fin n → E)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let v : Fin n → E := fun j => IsCMField.complexConj E (f (Pi.single j 1))
  have hpair : ∀ w : Fin n → E, ∑ j, IsCMField.complexConj E (v j) * w j = f w := by
    intro w
    conv_rhs => rw [pi_eq_sum_univ' w, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    simp only [v, IsCMField.complexConj_apply_apply]
  have hkill : ∀ w ∈ Λ.La, f w = 0 := fun w hw => hf (Submodule.subset_span hw)
  have hv : v ∈ Λ.La := (h v).2 fun w hw => by
    rw [hpair, hkill w hw]
    exact zero_mem _
  have hv0 : v = 0 := eq_zero_of_sum_conj v (by rw [hpair, hkill v hv])
  refine hf0 (LinearMap.ext fun w => ?_)
  rw [← hpair, hv0]
  simp

theorem isLat_of_unimod (Λ : GenLat E n) (h : Λ.Unimod) : IsLat Λ := by
  classical
  have hspan := span_eq_top_of_unimod Λ h
  refine ⟨?_, hspan⟩
  choose o ho0 ho using fun j : Fin n =>
    exists_mul_mem_of_mem_span Λ.La (x := Pi.single j 1) (hspan ▸ Submodule.mem_top)
  have hd : ∀ j, (∏ i, o i) • (Pi.single j 1 : Fin n → E) ∈ Λ.La := fun j => by
    rw [← Finset.prod_erase_mul _ o (Finset.mem_univ j), mul_smul]
    exact Λ.La.smul_mem _ (ho j)
  have hd0 : ∏ i, o i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ho0 i
  refine fg_of_smul_mem (o := IsCMField.ringOfIntegersComplexConj E (∏ i, o i))
    ((map_ne_zero_iff _ (IsCMField.ringOfIntegersComplexConj E).injective).2 hd0) fun x hx => ?_
  refine mem_stdMod.2 fun j => ?_
  obtain ⟨a, ha⟩ := (h _).1 (hd j) x hx
  refine ⟨a, Eq.trans ha ?_⟩
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)]
  rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, Algebra.smul_def, mul_one]
  congr 1

end GlobalTheory.GenusLatCompare
