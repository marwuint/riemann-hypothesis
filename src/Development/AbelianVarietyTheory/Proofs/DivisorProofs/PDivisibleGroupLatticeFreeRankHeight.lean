import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeEqRowSpaceOfSandwichDatum
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem GlobalTheory.PDivLat.latt_free_finrank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → Module.Free (Ainf p O) (latt G) ∧ Module.Finite (Ainf p O) (latt G) ∧ Module.finrank (Ainf p O) (latt G) = G.height := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG
  obtain ⟨D, e, fil, _lie, hal, _⟩ := hG
  obtain ⟨L, -⟩ := _root_.GlobalTheory.PDivLat.RowSpace.latt_eq_rowSpace p C v O hv ε hε G G.height D e fil hal
  haveI : Nontrivial (PreTilt O p) := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  refine ⟨Module.Free.of_equiv L, Module.Finite.equiv L, ?_⟩
  rw [← L.finrank_eq, Module.finrank_fin_fun]
