import Mathlib
import Formalism.LocalToGlobal.Columns.BrzColLatOneLattice

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality Formalism.HermitianLatticesTheory

section Orth

variable {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)

def brzo_perp (x : A.V) : Submodule (𝓞 K) A.V where
  carrier := {y | ∀ v, majAt A.b A.X v x y = 0}
  add_mem' := by
    intro a b ha hb v
    have h : majAt A.b A.X v x (a + b) = majAt A.b A.X v x a + majAt A.b A.X v x b := ((isSesq_maj A.b A.X) v).2.1 x a b
    rw [h, ha v, hb v, add_zero]
  zero_mem' := by
    intro v
    have h : majAt A.b A.X v x ((0 : K) • (0 : A.V)) = v.embedding (0 : K) * majAt A.b A.X v x 0 :=
      ((isSesq_maj A.b A.X) v).2.2.2 (0 : K) x 0
    simpa using h
  smul_mem' := by
    intro c y hy v
    have h : majAt A.b A.X v x (algebraMap (𝓞 K) K c • y) = v.embedding (algebraMap (𝓞 K) K c) * majAt A.b A.X v x y :=
      ((isSesq_maj A.b A.X) v).2.2.2 (algebraMap (𝓞 K) K c) x y
    rw [algebraMap_smul] at h
    rw [h, hy v, mul_zero]

variable {A} {γ : Type} [DecidableEq γ] (N : γ → Submodule (𝓞 K) A.V)

theorem brzo_orth_sup (horth : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0)
    (a : γ) (s : Finset γ) (ha : a ∉ s) : ∀ x ∈ N a, ∀ y ∈ ⨆ c ∈ s, N c,
    inner ℝ (realize A.b A.X x) (realize A.b A.X y) = 0 := by
  intro x hx y hy
  have hle : (⨆ c ∈ s, N c) ≤ brzo_perp A x :=
    iSup₂_le fun c hc z hz v => horth a c (fun h => ha (h ▸ hc)) x hx z hz v
  rw [Formalism.HN.HeightGram.inner_realize]
  exact Finset.sum_eq_zero fun v _ => by rw [hle hy v]; rfl

theorem hlat_orth_fin (hA : FrameOK A) (hfg : ∀ c, (N c).FG) (hne : ∀ c, N c ≠ ⊥)
    (horth : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0) (s : Finset γ) :
    Formalism.HN.deg (realize A.b A.X) (⨆ c ∈ s, N c) = ∑ c ∈ s, Formalism.HN.deg (realize A.b A.X) (N c) ∧
    (s.Nonempty → (⨆ c ∈ s, N c) ≠ ⊥ ∧ ∀ θ : ℝ, (∀ c ∈ s, Formalism.HN.muMax (realize A.b A.X) (N c) ≤ θ) →
      Formalism.HN.muMax (realize A.b A.X) (⨆ c ∈ s, N c) ≤ θ) := by
  have hlat : ∀ L : Submodule (𝓞 K) A.V, L.FG → Formalism.HN.IsLat (realize A.b A.X) L :=
    fun L hL => (Formalism.HN.plLat K A.V A.ι A.b A.X hA L hL).1
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, fun h => absurd h Finset.not_nonempty_empty⟩
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Finset.sum_empty]
    exact (Formalism.HN.satBasic (𝓞 K) A.V _ (realize A.b A.X) ⊥ (hlat ⊥ Submodule.fg_bot)).2.2.2.2.1
  | insert a s ha ih =>
    have hfs : (⨆ c ∈ s, N c).FG := Submodule.fg_biSup s N fun c _ => hfg c
    obtain ⟨-, h2, h3⟩ := (Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) A.V _ (realize A.b A.X)).2 (N a) (⨆ c ∈ s, N c) (hlat _ (hfg a)) (hlat _ hfs)
      (brzo_orth_sup N horth a s ha)
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    refine ⟨by rw [h2, ih.1], fun _ => ⟨fun h => hne a (eq_bot_iff.2 (h ▸ le_sup_left)), fun θ hθ => ?_⟩⟩
    by_cases hs : s.Nonempty
    · obtain ⟨i1, i2⟩ := ih.2 hs
      rw [(h3 (hne a) i1).1]
      exact max_le (hθ a (Finset.mem_insert_self _ _)) (i2 θ fun c hc => hθ c (Finset.mem_insert_of_mem hc))
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, sup_bot_eq]
      exact hθ a (Finset.mem_insert_self _ _)

theorem hlat_orth_sum [Fintype γ] [Nonempty γ] (hA : FrameOK A) (hfg : ∀ c, (N c).FG) (hne : ∀ c, N c ≠ ⊥)
    (horth : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0)
    (r : ℕ) (hr : 0 < r) (hrk : ∀ c, Formalism.HN.rkK (N c) = r) (hrkT : Formalism.HN.rkK (⨆ c, N c) = Fintype.card γ * r) :
    (withL A (⨆ c, N c)).mu = mean (fun c => (withL A (N c)).mu) ∧
    ∃ c, (withL A (⨆ c, N c)).muMax ≤ (withL A (N c)).muMax := by
  have hsup : (⨆ c, N c) = ⨆ c ∈ (Finset.univ : Finset γ), N c := by simp
  obtain ⟨h1, h2⟩ := hlat_orth_fin N hA hfg hne horth Finset.univ
  rw [← hsup] at h1 h2
  have hfT : (⨆ c, N c).FG := by rw [hsup]; exact Submodule.fg_biSup _ N fun c _ => hfg c
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hcard : (0 : ℝ) < (Fintype.card γ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hsl : ∀ c, Formalism.HN.slope (realize A.b A.X) (N c) =
      Formalism.HN.deg (realize A.b A.X) (N c) / ((Module.finrank ℚ K : ℝ) * r) := by
    intro c
    have := (Formalism.HN.plLat K A.V A.ι A.b A.X hA (N c) (hfg c)).2.1
    show Formalism.HN.deg (realize A.b A.X) (N c) / ((Formalism.HN.rk (realize A.b A.X) (N c) : ℕ) : ℝ) = _
    rw [this, hrk c]
    push_cast
    rfl
  have hslT : Formalism.HN.slope (realize A.b A.X) (⨆ c, N c) =
      (∑ c, Formalism.HN.deg (realize A.b A.X) (N c)) / ((Module.finrank ℚ K : ℝ) * (Fintype.card γ * r)) := by
    have := (Formalism.HN.plLat K A.V A.ι A.b A.X hA _ hfT).2.1
    show Formalism.HN.deg (realize A.b A.X) (⨆ c, N c) / ((Formalism.HN.rk (realize A.b A.X) (⨆ c, N c) : ℕ) : ℝ) = _
    rw [this, hrkT, h1]
    push_cast
    rfl
  constructor
  · show Formalism.HN.muDef A.b A.X (⨆ c, N c) = mean fun c => Formalism.HN.muDef A.b A.X (N c)
    unfold Formalism.HN.muDef mean
    rw [hslT]
    simp only [hsl]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
    field_simp
  · obtain ⟨c, -, hc⟩ := Finset.exists_max_image (Finset.univ : Finset γ)
      (fun c => Formalism.HN.muMax (realize A.b A.X) (N c)) Finset.univ_nonempty
    refine ⟨c, ?_⟩
    show Formalism.HN.muMaxDef A.b A.X (⨆ c, N c) ≤ Formalism.HN.muMaxDef A.b A.X (N c)
    unfold Formalism.HN.muMaxDef
    have := (h2 Finset.univ_nonempty).2 _ hc
    linarith

end Orth

section GSDOrth

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) (hf : S.Free)

open Classical in

def GSD.extZ (c : S.Cl) : S.V →ₗ[K] S.EqFun :=
  (S.resFree h S.outSec hf).symm.toLinearMap ∘ₗ LinearMap.single K (fun _ : S.Cl => S.V) c

def GSD.extL (c : S.Cl) : Submodule (𝓞 K) S.EqFun :=
  (S.Del (S.outSec.rep c)).map ((S.extZ h hf c).restrictScalars (𝓞 K))

end GSDOrth

end Formalism.L2.Col
