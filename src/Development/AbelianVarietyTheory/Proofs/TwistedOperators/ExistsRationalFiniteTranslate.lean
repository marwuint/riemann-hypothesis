import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalSplitStabilizerDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSplitPlaceFinitePointsOffPrimesOfSupported
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOfStabiliserMulInvEqStandardLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexLatticeEqAtMulSplitSupported

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedKappaDec

theorem eqAt_refl {D : D7} {N : ℕ} (q : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : EqAt D q L L := by
  refine ⟨1, Nat.coprime_one_left q, ?_, ?_⟩ <;>
  · intro x hx
    rwa [Nat.cast_one, one_smul]

theorem eqAt_symm {D : D7} {N : ℕ} {q : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h : EqAt D q L L₁) :
    EqAt D q L₁ L := by
  obtain ⟨s, hcop, hto, hback⟩ := h
  exact ⟨s, hcop, hback, hto⟩

theorem eqAt_trans {D : D7} {N : ℕ} {q : ℕ} {L L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h : EqAt D q L L₁)
    (h' : EqAt D q L₁ L₂) : EqAt D q L L₂ := by
  obtain ⟨a, ha, hL₁, hL₁'⟩ := h
  obtain ⟨b, hb, hL₂, hL₂'⟩ := h'
  refine ⟨a * b, Nat.Coprime.mul ha hb, fun x hx => ?_, fun x hx => ?_⟩
  ·
    have h1 : ((b : D.host.E) • ((a : D.host.E) • x)) ∈ L₂ := hL₂ _ (hL₁ x hx)
    rwa [smul_smul, mul_comm, ← Nat.cast_mul] at h1
  ·
    have h1 : ((a : D.host.E) • ((b : D.host.E) • x)) ∈ L := hL₁' _ (hL₂' x hx)
    rwa [smul_smul, ← Nat.cast_mul] at h1

end GlobalTheory.MovedKappaDec

end
