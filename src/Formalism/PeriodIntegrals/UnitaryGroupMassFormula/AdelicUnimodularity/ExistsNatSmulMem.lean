import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.SmulEqAlgebraMapMul
import Lemmata.GeneralBFactThirdMore.Key

noncomputable section

namespace PI.WAU

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "Af" => FiniteAdeleRing (𝓞 F) F

abbrev inclV (w : Fin n → E) : Fin n → E ⊗[F] Af := fun i => Formalism.UG.inclE (F := F) Af (w i)

theorem inclV_mem {L : Submodule (𝓞 E) (Fin n → E)} {w : Fin n → E} (hw : w ∈ L) :
    inclV (F := F) w ∈ lamAf (F := F) L :=
  Submodule.subset_span ⟨⟨w, hw⟩, rfl⟩

theorem one_tmul_mem_intAf {c : Af} (hc : c ∈ Ohat F) : ((1 : E) ⊗ₜ[F] c) ∈ IntAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)

theorem exists_nat_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ m : ℕ, 0 < m ∧ m • w ∈ L := by
  first | exact Bl.general_b_fact_third'.goal1 .. | (apply Bl.general_b_fact_third'.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third'.goal1 <;> assumption)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_lower (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ d : ℕ, 0 < d ∧ ∀ y : Fin n → E ⊗[F] Af, (∀ j, IntC b (y j)) → d • y ∈ lamAf (F := F) L := by
  classical
  choose m hm hmL using fun p : Fin n × ι => exists_nat_smul_mem L hL (Pi.single p.1 (b p.2))
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun y hy => ?_⟩
  have key : ∀ (j : Fin n) (k : ι) (c : Af), c ∈ Ohat F →
      (∏ p, m p) • Pi.single j (b k ⊗ₜ[F] c) ∈ lamAf (F := F) L := by
    intro j k c hc
    obtain ⟨q, hq⟩ : m (j, k) ∣ ∏ p, m p := Finset.dvd_prod_of_mem m (Finset.mem_univ (j, k))
    have hw : (∏ p, m p) • (Pi.single j (b k) : Fin n → E) ∈ L := by
      rw [hq, mul_comm, mul_smul]; exact nsmul_mem (hmL (j, k)) q
    have heq : (∏ p, m p) • (Pi.single j (b k ⊗ₜ[F] c) : Fin n → E ⊗[F] Af) =
        (⟨(1 : E) ⊗ₜ[F] c, one_tmul_mem_intAf hc⟩ : IntAf F E) •
          inclV (F := F) ((∏ p, m p) • (Pi.single j (b k) : Fin n → E)) := by
      funext i
      by_cases hij : i = j
      · subst hij
        simp only [Pi.smul_apply, Pi.single_eq_same, Subring.smul_def, smul_eq_mul, Formalism.UG.inclE,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one]
        rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F, TensorProduct.smul_tmul']
        simp only [inclV, Pi.smul_apply, Pi.single_eq_same, Formalism.UG.inclE,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      · simp [Pi.single_eq_of_ne hij, Subring.smul_def, Formalism.UG.inclE, inclV]
    rw [heq]
    exact Submodule.smul_mem _ _ (inclV_mem hw)
  have hy' : y = ∑ j, ∑ k, (Pi.single j (b k ⊗ₜ[F] coord b (y j) k) : Fin n → E ⊗[F] Af) := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := emb_coord b (y j)
    simp only [emb] at h1
    conv_lhs => rw [← h1]
    exact map_sum (AddMonoidHom.single (fun _ : Fin n => E ⊗[F] Af) j) _ _
  rw [hy', Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Finset.smul_sum]
  exact Submodule.sum_mem _ fun k _ => key j k _ (hy j k)

end PI.WAU
