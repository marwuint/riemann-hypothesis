import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageDerivativeL1Bound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness

noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.ApproxK

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveK
open GlobalTheory.CompanionTheory.KerUniq

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace msK

variable {n : ℕ}

local instance : BorelSpace (UK n) := ⟨rfl⟩
local instance : CompactSpace (UK n) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
local instance : SecondCountableTopology (Mat n) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
local instance : LocallyCompactSpace (Mat n) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
local instance : ProperSpace (Mat n) :=
  inferInstanceAs (ProperSpace (Fin n → Fin n → ℂ))
local instance : SecondCountableTopology (G n) :=
  have : SecondCountableTopology (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology
local instance : LocallyCompactSpace (G n) := inferInstanceAs (LocallyCompactSpace (Mat n)ˣ)
local instance : SecondCountableTopology (UK n) :=
  (Topology.IsEmbedding.subtypeVal (p := fun x => x ∈ unitaryGroup (Fin n) ℂ)).secondCountableTopology
local instance : (nu n).IsHaarMeasure := by unfold nu; infer_instance
local instance : IsFiniteMeasure (nu n) := CompactSpace.isFiniteMeasure
local instance : (nu n).IsMulRightInvariant :=
  ⟨fun g => GlobalTheory.CompactRight.map_mul_right_eq_of_mem_compact (nu n) ⊤
    (by simpa using isCompact_univ) g (Subgroup.mem_top g)⟩

end GlobalTheory.CompanionTheory.ApproxK
