import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GluePlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EulerProductInductionSupported
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.GlobTw

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

private theorem sum_card_le {α ι : Type*} [Fintype ι] (Q : ι → α → Prop) (hQ : ∀ c c' y, Q c y → Q c' y → c = c')
    (s : Multiset α) : ∑ c, (s.filter (Q c)).card ≤ (s.filter fun y => ∃ c, Q c y).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons y s ih =>
    simp only [Multiset.filter_cons, Multiset.card_add, Finset.sum_add_distrib]
    refine add_le_add ?_ ih
    by_cases h : ∃ c, Q c y
    · obtain ⟨c, hc⟩ := h
      rw [if_pos ⟨c, hc⟩, Finset.sum_eq_single c (fun b _ hb => by rw [if_neg fun h => hb (hQ _ _ _ h hc)]; rfl) (by simp),
        if_pos hc]
    · rw [if_neg h, Finset.sum_eq_zero fun b _ => by rw [if_neg fun h' => h ⟨b, h'⟩]; rfl]
      exact Nat.zero_le _

private theorem comb {W : Type} [Fintype W] {α : W → Type 1} (r : Setoid (Fin 3)) (s : ∀ w, Multiset (α w))
    (Q : ∀ w, Fin 3 → α w → Prop) (f : W → ℕ) (hf : ∀ w, 0 < f w) (hs : ∀ w, (s w).card ≤ 3)
    (hQ : ∀ w i i' y, Q w i y → Q w i' y → r i i')
    (h : ∀ i, (Finset.univ.filter fun i' => r i' i).card * ∑ w, f w = ∑ w, f w * ((s w).filter (Q w i)).card) :
    ∀ w, ∀ y ∈ s w, ∃ i, Q w i y := by
  have h3 : ∑ c : Quotient r, (Finset.univ.filter fun i' => r i' c.out).card = 3 := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := Quotient.mk r) (by simp)
    rw [Finset.card_univ, Fintype.card_fin] at this
    refine (Finset.sum_congr rfl fun c _ => congrArg _ (Finset.filter_congr fun i _ => ?_)).trans this.symm
    exact Quotient.mk_eq_iff_out.symm
  have hle : ∀ w, ∑ c : Quotient r, ((s w).filter (Q w c.out)).card ≤ ((s w).filter fun y => ∃ c : Quotient r, Q w c.out y).card :=
    fun w => sum_card_le (fun c : Quotient r => Q w c.out)
      (fun c c' y h h' => by rw [← c.out_eq, ← c'.out_eq]; exact Quotient.sound (hQ w _ _ y h h')) (s w)
  have hle3 : ∀ w, ∑ c : Quotient r, ((s w).filter (Q w c.out)).card ≤ 3 := fun w =>
    (hle w).trans ((Multiset.card_le_card (Multiset.filter_le _ _)).trans (hs w))
  have heq : ∑ w, f w * ∑ c : Quotient r, ((s w).filter (Q w c.out)).card = ∑ w, f w * 3 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_congr rfl fun (c : Quotient r) _ => h c.out, ← Finset.sum_mul, h3, ← Finset.sum_mul,
      mul_comm]
  intro w y hy
  have h1 := (Finset.sum_eq_sum_iff_of_le fun w _ => Nat.mul_le_mul_left (f w) (hle3 w)).1 heq w (Finset.mem_univ w)
  have h2 := Nat.eq_of_mul_eq_mul_left (hf w) h1
  have h4 := Multiset.eq_of_le_of_card_le (Multiset.filter_le (fun y => ∃ c : Quotient r, Q w c.out y) (s w))
    ((hs w).trans (h2.symm.le.trans (hle w)))
  obtain ⟨c, hc⟩ := Multiset.filter_eq_self.1 h4 y hy
  exact ⟨_, hc⟩

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

