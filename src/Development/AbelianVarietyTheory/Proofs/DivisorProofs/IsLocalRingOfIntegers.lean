import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantPDivGroupOmegaTrivialHodgeTateBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInOfIntegers

noncomputable section

open WittVector CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.ConstDatum

theorem isLocalRing_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsLocalRing O := ReciprocityTheory.PGsh.Up.isLocal_of_integers hv

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem etale_al (ε : PreTilt O p) (h : ℕ) (y : Fin h → O) : (etale ε h).al y = y := by
  simp [Datum.al, etale, Matrix.map_one _ (map_zero _) (map_one _)]

theorem theta_mu {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : fontaineTheta O p (Sandwich.mu ε) = 0 := by
  rw [Sandwich.mu, map_sub, fontaineTheta_teichmuller, map_one, sub_eq_zero]
  exact hε.zeta_zero

theorem etale_bb {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (h : ℕ) (y : Fin h → O) :
    (etale ε h).bb y = 0 := by
  ext i
  simp [Datum.bb, etale, Matrix.mulVec, dotProduct, theta_mu hε]

theorem etale_Fil {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (h : ℕ) : (etale ε h).Fil = ⊤ :=
  eq_top_iff.2 fun y _ => etale_bb hε h y

end GlobalTheory.ConstDatum

open GlobalTheory.ConstDatum in

theorem GlobalTheory.PDivLat.hasDatum_of_isConst : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, IsConst G → HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG
  haveI := GlobalTheory.PointGroup.isIntegrallyClosedIn_of_integers hv
  haveI := isLocalRing_of_integers hv
  obtain ⟨hω, hbij⟩ := _root_.GlobalTheory.ConstHT.omega_const p C v O hv G hG
  haveI := GlobalTheory.PointGroup.finite_tate hv G
  haveI := GlobalTheory.PointGroup.free_tate hv G
  have hrank : Module.finrank ℤ_[p] G.Tate = G.height := G.finrank_tate C
  let e : G.Tate ≃ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hrank, Module.finrank_fin_fun])
  let b : Module.Basis (Fin G.height) ℤ_[p] G.Tate := Module.Basis.ofEquivFun e
  let Φ := LinearEquiv.ofBijective _ (hbij G.height b)
  let D := etale ε G.height
  have hF : D.Fil = ⊤ := etale_Fil hε G.height
  let fil : G.dual.omega ≃ₗ[O] D.Fil := Φ.symm ≪≫ₗ (LinearEquiv.ofTop _ hF).symm
  haveI : Subsingleton G.Lie :=
    ⟨fun f g => LinearMap.ext fun w => by rw [Subsingleton.elim w 0, map_zero, map_zero]⟩
  haveI : Subsingleton ((Fin G.height → O) ⧸ D.Fil) :=
    ⟨fun a b => by
      obtain ⟨a, rfl⟩ := D.Fil.mkQ_surjective a
      obtain ⟨b, rfl⟩ := D.Fil.mkQ_surjective b
      exact (Submodule.Quotient.eq D.Fil).2 (by rw [hF]; exact Submodule.mem_top)⟩
  refine ⟨D, e, fil, LinearEquiv.ofSubsingleton _ _, fun t => ?_, fun x χ => ?_⟩
  · rw [etale_al]
    change toO e t = ((LinearEquiv.ofTop _ hF).symm (Φ.symm (hodgeTate G t)) : Fin G.height → O)
    rw [LinearEquiv.coe_ofTop_symm_apply, LinearEquiv.eq_symm_apply]
    change Fintype.linearCombination O (fun i => hodgeTate G (b i)) (toO e t) = hodgeTate G t
    rw [Fintype.linearCombination_apply]
    have hb : b.equivFun = e := Module.Basis.equivFun_ofEquivFun e
    conv_rhs => rw [← b.sum_equivFun t]
    rw [map_sum, hb]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hodgeTate_smul (padicToO p O)]
    rfl
  · rw [Subsingleton.elim x 0]
    simp [pairingO]
