import Mathlib
import Formalism.LocalToGlobal.Columns.ColFormsLemmas
import Formalism.LocalToGlobal.Columns.LevGCount
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Columns.Inputs
import Formalism.GL3MeanSquares.HookFormulaTorsion.OneAddInvPowLeExpOne
import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree
import Formalism.HermitianLattices.FinalMass

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Frame

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

structure FrameAt (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 K) V) {n : ℕ}
    (β : V → (Fin n → 𝓞 K ⧸ w.asIdeal)) : Prop where
  add : ∀ x ∈ localization₂ w.asIdeal N, ∀ y ∈ localization₂ w.asIdeal N, β (x + y) = β x + β y
  smul : ∀ (a : 𝓞 K), ∀ x ∈ localization₂ w.asIdeal N, β (a • x) = Ideal.Quotient.mk w.asIdeal a • β x
  off : ∀ x, x ∉ localization₂ w.asIdeal N → β x = 0
  surj : ∀ c, ∃ x ∈ N, β x = c
  ker : ∀ x ∈ N, β x = 0 → x ∈ w.asIdeal • N

namespace LinOn

end LinOn

end Frame

section Mass

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

abbrev UniLat : Type :=
  {N : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E N ∧ IsUnimodular (hStd E n) N}

variable {E n}

theorem gmap_unimodular {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n) {N : Submodule (𝓞 E) (Sp E n)}
    (hN : IsUnimodular (hStd E n) N) : IsUnimodular (hStd E n) (gmap g N) := by
  unfold IsUnimodular at *
  rw [dual_gmap g hg, hN]

instance : MulAction (UF E n) (UniLat E n) where
  smul g N := ⟨gmap g.1 N.1, gmap_lattice g.1 N.1 N.2.1, gmap_unimodular g.2 N.2.2⟩
  one_smul N := Subtype.ext (Submodule.map_id N.1)
  mul_smul a b N := Subtype.ext (by
    change N.1.map _ = (N.1.map _).map _
    rw [← Submodule.map_comp]
    rfl)

theorem UniLat.smul_val (g : UF E n) (N : UniLat E n) : (g • N).1 = gmap g.1 N.1 := rfl

variable (E n)

abbrev autU (N : UniLat E n) : Subgroup (UF E n) := MulAction.stabilizer (UF E n) N

variable {E n}

theorem finite_autU (hE : PosStar E) (N : UniLat E n) : Finite (autU E n N) := by
  have hA := final_autFinite E (Sp E n) (hStd E n) hStd_isSymm (hStd_pos hE) N.1 N.2.1
  have : Finite {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g N.1 = N.1} := hA
  refine Finite.of_injective
    (fun a : autU E n N => (⟨a.1.1, a.1.2, congrArg Subtype.val a.2⟩ :
      {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g N.1 = N.1})) ?_
  intro a b hab
  exact Subtype.ext (Subtype.ext (show a.1.1 = b.1.1 from
    congrArg (fun g : {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g N.1 = N.1} => g.1) hab))

end Mass

section Count

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.lat (d : DecoSet E n ST SG) : UniLat E n := ⟨d.1.N, d.2.lat, d.2.uni⟩

end Count

section Idx

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  (Λ : LevFam E K n SG)

def LevFam.idx : ℕ := ∏ w : SG, (Λ w).H.index

end Idx

section IdxQ

theorem card_res {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    Nat.card (𝓞 E ⧸ w.asIdeal) = Ideal.absNorm w.asIdeal := rfl

end IdxQ

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem rankN_zero (R : Ranks) : R.N 0 = R.k := by
  simp [Ranks.N]

variable (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

section Inst

open Finset Formalism.LogVandermondeBounds.StandardLattice

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def hcSeq (u : Pr.Word) (τ : X.Tau) : ℕ → ℝ := fun i => if h : i < R.k then (((W.hc u τ).u ⟨i, h⟩ : ℚ) : ℝ) else 0

theorem vandN_congr {x y : ℕ → ℝ} {N : ℕ} (h : ∀ i j, i < N → j < N → x i - x j = y i - y j) : vandN x N = vandN y N := by
  unfold vandN
  exact Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj =>
    h i j (Finset.mem_range.1 hi) (Finset.mem_Ico.1 hj).2

end Inst

section Unram

theorem cm_unramified_of_field_conditions {X : Fields} (hX : X.AbelianUnramifiedExtensionConditions) : IsCMUnram X.E := by
  refine ⟨hX.ok.cplxE, hX.ok.conjE, ?_⟩
  intro P hP
  by_contra hcon
  have hall : ∀ θ : 𝓞 X.E, θ - X.conjO θ ∈ P := by
    intro θ
    by_contra h
    exact hcon ⟨θ, X.conjO θ, rfl, h⟩
  have hq : Algebra.IsQuadraticExtension X.F X.E := { finrank_eq_two' := hX.ok.rankE }
  let c : Gal(X.E/X.F) := AlgEquiv.ofRingEquiv (f := starRingAut) (fun r => hX.ok.star_F r)
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField X.E)
  have hPp : P.IsPrime := hP.isPrime
  have hun := hX.unram ⟨P, hPp, hP0⟩
  have hlo : P.LiesOver (P.under (𝓞 X.F)) := ⟨rfl⟩
  have hp0 : P.under (𝓞 X.F) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 X.F) hP0
  have hcard : Nat.card (P.inertia Gal(X.E/X.F)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(X.E/X.F)) (P.under (𝓞 X.F)) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 X.F)) P Gal(X.E/X.F),
      ← Ideal.ramificationIdx'_eq_ramificationIdx (P.under (𝓞 X.F)) P hp0]
    by_contra h
    exact hun ((Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).mp h)
  have hc : c ∈ P.inertia Gal(X.E/X.F) := by
    intro x
    have h1 : c • x - x = -(x - X.conjO x) := by
      rw [neg_sub]
      rfl
    rw [h1]
    exact P.neg_mem (hall x)
  have hc1 : c = 1 := by
    have hb := (Subgroup.card_eq_one (H := P.inertia Gal(X.E/X.F))).mp hcard
    rw [hb] at hc
    exact hc
  have hτ : Nonempty X.Tau := by
    rw [← Fintype.card_pos_iff, hX.ok.card_Tau]
    exact Module.finrank_pos
  obtain ⟨τ⟩ := hτ
  apply hX.ok.emb_ne τ τ
  ext x
  have h2 : star x = x := congrArg (fun s : Gal(X.E/X.F) => s x) hc1
  show X.emb τ x = X.emb τ (star x)
  rw [h2]

end Unram

end Formalism.L2.Col
