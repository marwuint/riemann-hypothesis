import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OperatorSequenceSumEpiStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSequenceCoherent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventuallyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformSpanEventually
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedVanishingSectionsSpan

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem uniformGen_of_gradedNoeth : GradedNoeth → UniformVanishing → UniformGen := by
  intro hN hV A _ _ X _ _ H hH k M T d hM
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := hH.compactSpace
  have hcoh := _root_.GlobalTheory.CompanionTheory.GE.isCoherent_kerSeq hM
  obtain ⟨d', hd'⟩ := _root_.GlobalTheory.CompanionTheory.GE.Uniform.span_range_eq_top_uniform (KerSeq.kerOp T hM.comm d) (fun e => (hcoh e).1)
    (GlobalTheory.T.kernel_operators_span_eventually hN hM)
  have hK : OpSeq k (KerSeq.kerSeq T d) (KerSeq.kerOp T hM.comm d) d' :=
    ⟨hcoh, KerSeq.kerOp_comm T hM.comm d, hd'⟩
  obtain ⟨n₀, hn₀⟩ := hV (A := A) H hH k _ _ d' hK
  refine ⟨n₀, fun n hn e he => ?_⟩
  obtain ⟨e₀, rfl⟩ := Nat.exists_eq_add_of_le he
  haveI := GlobalTheory.T.operator_sequence_sum_epi hM e₀
  exact _root_.GlobalTheory.CompanionTheory.GE.span_range_twist_eq_top (GlobalTheory.lbZPow H n) (GlobalTheory.Twist.isLB_lbZPow hH.isLB n) (fun i => T i (d + e₀))
    (kernel.ι _) (kernel.condition _) (KerSeq.kerSC_shortExact T d e₀) (hn₀ n hn e₀ 1 one_pos)

end GlobalTheory.CompanionTheory.GE
