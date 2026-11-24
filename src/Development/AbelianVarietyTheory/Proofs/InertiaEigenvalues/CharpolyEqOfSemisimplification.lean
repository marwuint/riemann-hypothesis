module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SemisimplificationCharpoly

private theorem charpoly_eq_of_filtration_graded_eq {k : Type} [Field k] (n : ℕ) :
    ∀ {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (G : ℕ → Submodule k V)
      (f g : Module.End k V), Monotone G → G 0 = ⊥ → G n = ⊤ → (∀ i, ∀ x ∈ G i, f x ∈ G i) →
      (∀ i, ∀ x ∈ G (i + 1), g x - f x ∈ G i) → LinearMap.charpoly f = LinearMap.charpoly g := by
  induction n with
  | zero =>
    intro V _ _ _ G f g _ h0 hn _ _
    have hV : ∀ x : V, x = 0 := by
      intro x
      have hx : x ∈ G 0 := by rw [hn]; exact Submodule.mem_top
      rw [h0] at hx
      exact (Submodule.mem_bot k).mp hx
    have hfg : f = g := by
      ext x
      rw [hV x, map_zero, map_zero]
    rw [hfg]
  | succ n ih =>
    intro V _ _ _ G f g hmono h0 hn hf hd

    have hg : ∀ i, ∀ x ∈ G i, g x ∈ G i := by
      intro i x hx
      cases i with
      | zero =>
        rw [h0] at hx
        rw [(Submodule.mem_bot k).mp hx, map_zero]
        exact Submodule.zero_mem _
      | succ j =>
        have e : g x = f x + (g x - f x) := by abel
        rw [e]
        exact Submodule.add_mem _ (hf _ x hx) (hmono (Nat.le_succ j) (hd j x hx))
    set A := G n with hA
    rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ A f (hf n),
      GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ A g (hg n)]
    congr 1
    ·
      refine ih (fun i => (G i).comap A.subtype) (f.restrict (hf n)) (g.restrict (hg n))
        (fun i j hij => Submodule.comap_mono (hmono hij)) ?_ ?_ ?_ ?_
      · rw [h0, Submodule.comap_bot, Submodule.ker_subtype]
      · exact Submodule.comap_subtype_self A
      · exact fun i x hx => hf i x hx
      · exact fun i x hx => hd i x hx
    ·
      congr 1
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.mapQ_apply]
      rw [Submodule.Quotient.eq]
      have hx : x ∈ G (n + 1) := by rw [hn]; exact Submodule.mem_top
      have := hd n x hx
      rwa [← neg_mem_iff, neg_sub] at this

theorem charpoly_eq_of_filtration {k : Type} [Field k] (n : ℕ) :
    ∀ {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (F : ℕ → Submodule k V)
      (f g : Module.End k V), F 0 = ⊥ → F n = ⊤ → (∀ i, ∀ x ∈ F i, f x ∈ F i) →
      (∀ i, ∀ x ∈ F (i + 1), g x - f x ∈ F i) → LinearMap.charpoly f = LinearMap.charpoly g := by
  intro V _ _ _ F f g h0 hn hf hd

  refine charpoly_eq_of_filtration_graded_eq n (fun i => partialSups F i) f g (partialSups F).monotone ?_ ?_ ?_ ?_
  · simp only [partialSups_zero, h0]
  · exact eq_top_iff.mpr (hn ▸ le_partialSups F n)
  · intro i
    have hle : partialSups F i ≤ (partialSups F i).comap f := by
      exact partialSups_le F i _ (fun j hj x hx => le_partialSups_of_le F hj (hf j x hx))
    exact fun x hx => hle hx
  · intro i
    have hle : partialSups F (i + 1) ≤ (partialSups F i).comap (g - f) := by
      refine partialSups_le F (i + 1) _ (fun j hj x hx => ?_)
      cases j with
      | zero =>
        rw [h0] at hx
        rw [(Submodule.mem_bot k).mp hx]
        exact Submodule.zero_mem _
      | succ m =>
        exact le_partialSups_of_le F (Nat.succ_le_succ_iff.mp hj) (hd m x hx)
    exact fun x hx => hle hx

theorem charpoly_eq : ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (s : Representation k Γ W) (ρ : Representation k Γ V),
    GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ →
      ∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (ρ g) := by
  intro k Γ _ _ W _ _ _ V _ _ _ s ρ hss g
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf at hss
  obtain ⟨-, m, Ws, e, hst, hint, hρ⟩ := hss
  have hsj : ∀ j, ∀ x ∈ Ws j, s g x ∈ Ws j := by
    intro j x hx
    have h := hst j
    unfold Stable at h
    exact h g x hx

  let H : ℕ → Submodule k W := fun i => ⨆ (j : Fin m) (_ : (j : ℕ) < i), Ws j
  have hH : ∀ i, ∀ x ∈ H i, s g x ∈ H i := by
    intro i
    have hle : H i ≤ (H i).comap (s g) :=
      iSup₂_le fun j hj x hx =>
        (le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < i) => Ws j) j hj) (hsj j x hx)
    exact fun x hx => hle hx
  rw [← e.charpoly_conj (s g)]
  refine charpoly_eq_of_filtration m (fun i => (H i).map (e : W →ₗ[k] V)) (e.conj (s g)) (ρ g)
    ?_ ?_ ?_ ?_
  · have h0 : H 0 = ⊥ := by simp [H]
    simp only [h0, Submodule.map_bot]
  · have hm : H m = ⊤ := by
      rw [eq_top_iff, ← hint.submodule_iSup_eq_top]
      exact iSup_le fun j => le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < m) => Ws j) j j.isLt
    simp only [hm, Submodule.map_top, LinearEquiv.range]
  · intro i x hx
    rw [Submodule.mem_map_equiv] at hx ⊢
    simpa [LinearEquiv.conj_apply] using hH i _ hx
  · intro i x hx
    rw [Submodule.mem_map_equiv] at hx
    have hle : H (i + 1) ≤ ((H i).map (e : W →ₗ[k] V)).comap
        ((ρ g - e.conj (s g)) ∘ₗ (e : W →ₗ[k] V)) := by
      refine iSup₂_le fun j hj v hv => ?_
      have hsub : (⨆ j' ∈ Set.Iio j, Ws j') ≤ H i :=
        iSup₂_le fun j' hj' => le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < i) => Ws j) j'
          (lt_of_lt_of_le (Fin.lt_def.mp (Set.mem_Iio.mp hj')) (Nat.lt_succ_iff.mp hj))
      have h1 := Submodule.map_mono (f := (e : W →ₗ[k] V)) hsub (hρ j g v hv)
      simpa [LinearEquiv.conj_apply] using h1
    simpa using hle hx

end GlobalTheory.SemisimplificationCharpoly
