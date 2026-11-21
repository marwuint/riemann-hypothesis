import Formalism.LocalRingCardinality.DataParams₂
import Formalism.ThetaLiftIndependence.Statement
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Ipindep
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.LatLiftIndep
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.DetSwap
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.LocalRingCardinality.HostCls
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameCyclicGenerator
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain

section ranks

variable (R : Ranks)

theorem Ranks.k_ge : 5 ≤ R.k := by
  have h1 := R.two_le_m
  have h2 := R.m_add_three_le_k
  omega

theorem Ranks.rS_two : 2 * R.rS + 2 = R.m := by
  obtain ⟨a, ha⟩ := R.m_even
  have h1 := R.two_le_m
  simp only [Ranks.rS]
  omega

theorem Ranks.r_eq : R.r + 1 = R.k + R.m := by
  have h1 := R.two_le_m
  simp only [Ranks.r]
  omega

end ranks

theorem rank_base_space : RankBaseSpaceEq := by
  intro R
  have h1 := R.rS_two
  have h2 := R.two_le_m
  simp only [Ranks.N, Ranks.r]
  omega

theorem factXm : FactXm := by
  intro R
  have h2 := R.two_le_m
  simp only [Ranks.N, Ranks.rankX', Ranks.r, mul_add, mul_one]
  omega

theorem factNEven : FactNEven := by
  intro R j
  simp only [Ranks.N]
  exact R.k_even.add (Even.mul_left R.t_odd.add_one _)

theorem factWtZero : FactWtZero := by
  intro R ι _ hc C hZ c
  haveI := C.stabGrp 0 c
  have h1 : Nat.card (C.stab 0 c) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hZ c, ⟨1⟩⟩
  simp only [ColumnChain.wt, h1, Nat.cast_one, inv_one]

namespace Rows

end Rows

theorem factNatW : FactNatW := by
  intro N lam
  have key : ∀ i : Fin N, lam.detShift ≤ lam.w i := by
    intro i
    have hi := i.2
    have hN : 0 < N := by omega
    simp only [DomWeight.detShift, dif_pos hN]
    exact lam.anti (show i ≤ ⟨N - 1, by omega⟩ from Fin.le_iff_val_le_val.mpr (show i.val ≤ N - 1 by omega))
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    simp only [DomWeight.natW]
    exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)
  · intro i
    have := key i
    simp only [DomWeight.natW]
    omega
  · intro h
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos h]
    simp

theorem bridge_sigRank_holds : Spaces.bridge_sigRank := by
  intro E _ _ _ S hS τ
  obtain ⟨e, -, -⟩ := hS τ
  have h := Fintype.card_congr e
  simp only [Fintype.card_fin, Fintype.card_sum] at h
  omega

theorem factWmPosDef (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] : FactWmPosDef R F E := by
  intro S τ
  have h1 : 1 ≤ R.m := by
    have := R.two_le_m
    omega
  rw [S.W_sigval R.m h1 le_rfl τ, S.W_rank R.m h1 le_rfl]
  simp only [Ranks.sigW, Ranks.r, Nat.sub_self]

section host

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem orderOf_unit_class_eq_two_pow (e : ℕ) : orderOf (hcl e (u5 (e + 2))) = 2 ^ e :=
  (Formalism.FrobeniusOrbits.Final.host_field.2.1 e).2.2.2.2.2.2.2.1

theorem card_HGrp (e : ℕ) : Nat.card (HGrp e) = 2 ^ e :=
  (Formalism.FrobeniusOrbits.Final.host_field.2.1 e).2.2.2.2.2.2.1

theorem iotaH_add (e : ℕ) (i j : ZMod (2 ^ e)) : iotaH e (i + j) = iotaH e i * iotaH e j := by
  simp only [iotaH]
  rw [← pow_add, ZMod.val_add]
  have h := pow_mod_orderOf (hcl e (u5 (e + 2))) (i.val + j.val)
  rw [orderOf_unit_class_eq_two_pow e] at h
  exact h

theorem iotaH_zero (e : ℕ) : iotaH e 0 = 1 := by
  simp only [iotaH, ZMod.val_zero, pow_zero]

theorem iotaH_bijective (e : ℕ) : Function.Bijective (iotaH e) := by
  have inj : Function.Injective (iotaH e) := by
    intro i j hij
    simp only [iotaH] at hij
    rw [pow_inj_mod, orderOf_unit_class_eq_two_pow e, Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hij
    exact ZMod.val_injective _ hij
  exact inj.bijective_of_nat_card_le (by rw [card_HGrp, Nat.card_zmod])

theorem iotaH_iotaHInv (e : ℕ) (h : HGrp e) : iotaH e (iotaHInv e h) = h := Function.rightInverse_invFun (iotaH_bijective e).surjective h

theorem bridge_star_holds : bridge_star := by
  intro R H x
  have := H.isCMField_hostE
  apply H.φ₀.injective
  change H.φ₀ (NumberField.IsCMField.complexConj H.E x) = H.φ₀ (H.conj x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj, H.conjE_apply]

theorem factCardPsi : FactCardPsi := fun R H => ⟨R.natCard_Psi, H.der.cmType.2.1⟩

theorem factEmb : FactEmb := by
  intro R H
  refine ⟨(H.hostEmb H.φ₀).comp H.gal.symm.bijective, fun g => ?_⟩
  have hc := H.der.cmType.2.2 H.φ₀ H.φ₀_mem (H.sigmaOf g)
  have hg : H.gal (H.sigmaOf g) = g := MulEquiv.apply_symm_apply _ _
  rw [hg] at hc
  exact hc

theorem factPlaces : FactPlaces := fun φ => ⟨φ.mem_Psi_iff_tau, φ.ramifiedTau1_ne_ramifiedTau2⟩

theorem factTopsThick : FactTopsThick := by
  intro R H
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [Host.topPlaces, Finset.mem_image] at hg
    obtain ⟨t, -, rfl⟩ := hg
    exact R.tau1_mem_Psi t
  · intro g hg
    simp only [Host.thickPlaces, Finset.mem_image] at hg
    obtain ⟨s, -, rfl⟩ := hg
    exact R.doubling_mem_character_set _
  · rw [Finset.disjoint_left]
    intro g h1 h2
    simp only [Host.topPlaces, Host.thickPlaces, Finset.mem_image] at h1 h2
    obtain ⟨t, -, rfl⟩ := h1
    obtain ⟨s, -, hs⟩ := h2
    exact R.ramifiedTau1_ne_ramifiedTau2 _ _ hs.symm
  · unfold Host.topPlaces
    rw [Finset.card_image_of_injective _ R.tau1_injective]
  · have hlt : ∀ s ∈ H.T2, s < R.n0 := by
      intro s hs
      have hL := H.two_le_Lw
      have := H.second_set_range s hs
      have : s ≤ 4 * H.Lw * s := Nat.le_mul_of_pos_left s (by omega)
      omega
    unfold Host.thickPlaces
    rw [Finset.card_image_of_injOn]
    intro s hs s' hs' h
    exact R.dig_inj (hlt s hs) (hlt s' hs') (add_right_cancel (R.doubling_injective h))

theorem factRd : FactRd := by
  intro R H
  refine ⟨H.der.rd_ge, H.der.rd_le, ?_⟩
  have h : (2 * R.f : ℝ) = 4 * R.ord := by
    simp only [Ranks.f, Ranks.n]
    push_cast
    ring
  rw [h]
  exact H.der.rd_sq_ge

theorem factMMUnimodular : FactMMUnimodular := fun _ H x => H.der.unimodular H.𝔟 H.𝔟_spec.1 x

theorem factClassFrob : FactClassFrob := by
  intro R H p _ hp P _ _ σ hσ
  have hc := H.hostClasses p hp P σ hσ
  have hpr : p.Prime := Fact.out
  have hps := Formalism.HC.HostRaw.notMem_small_of_not_dvd hp
  have hpq := Formalism.HC.HostRaw.ne_q_of_not_dvd hp
  have hpd := Formalism.HC.HostRaw.ne_d_of_not_dvd hp
  have cop : Int.gcd (-(H.d : ℤ)) (p : ℤ) = 1 := by
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes H.d_prime hpr).mpr (Ne.symm hpd)
  have hJd := jacobiSym.eq_one_or_neg_one cop
  have hJq := H.psAt_eq_one_or (hpr.coprime_iff_not_dvd.2 hp)
  simp only [Host.cls, primeClass, if_neg hps, if_neg hpq, if_neg hpd]
  rcases hJd with h1 | h1 <;> rcases hJq with h2 | h2 <;> simp [h1, h2] at hc ⊢ <;> tauto

end host

section sig

open Matrix

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_expand (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ a, ∑ b, star (S.frame.repr x a) * S.gram a b * S.frame.repr y b := by
  have key : ∀ u : S.V, S.hT u y = ∑ b, S.hT u (S.frame b) * S.frame.repr y b := by
    intro u
    conv_lhs => rw [← S.frame.sum_repr y]
    rw [map_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [LinearMap.map_smul, smul_eq_mul, mul_comm]
  have key2 : ∀ b, S.hT x (S.frame b) = ∑ a, star (S.frame.repr x a) * S.hT (S.frame a) (S.frame b) := by
    intro b
    conv_lhs => rw [← S.frame.sum_repr x]
    rw [map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  rw [key x]
  simp only [key2, Finset.sum_mul, HSpace.gram]
  exact Finset.sum_comm

theorem gram_family (S : HSpace E) {ι : Type} [Fintype ι] (w : ι → S.V) :
    (Matrix.of fun i j => S.hT (w i) (w j)) =
      (Matrix.of fun a i => S.frame.repr (w i) a)ᴴ * S.gram *
        Matrix.of fun a i => S.frame.repr (w i) a := by
  ext i j
  simp only [Matrix.of_apply]
  rw [hT_expand]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem map_family (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    {ι : Type} [Fintype ι] (w : ι → S.V) :
    (Matrix.of fun i j => S.hT (w i) (w j)).map τ =
      ((Matrix.of fun a i => S.frame.repr (w i) a).map τ)ᴴ * S.gram.map τ *
        (Matrix.of fun a i => S.frame.repr (w i) a).map τ := by
  rw [gram_family, Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map τ (fun a => hτ a)]

theorem sig_family (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → S.V) {p q p' q' : ℕ}
    (h : Formalism.UG.HasSignature ((Matrix.of fun i j => S.hT (w i) (w j)).map τ) p q)
    (hS : Formalism.UG.HasSignature (S.gram.map τ) p' q') : p + q' ≤ S.rank ∧ p' + q ≤ S.rank := by
  obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data _ p q h
  obtain ⟨-, QS, hQS⟩ := Formalism.UG.P.sig_data _ p' q' hS
  rw [map_family S τ hτ w] at hQ
  have hQ' : (((Matrix.of fun a i => S.frame.repr (w i) a).map τ) * Q)ᴴ * S.gram.map τ *
      (((Matrix.of fun a i => S.frame.repr (w i) a).map τ) * Q) = Formalism.UG.Jpq p q := by
    rw [Matrix.conjTranspose_mul]
    simpa [Matrix.mul_assoc] using hQ
  have h1 := Formalism.UG.P.sig_dim (S.gram.map τ) _ hQ' QS hQS
  have h2 := Formalism.UG.P.sig_dim (S.gram.map τ) QS hQS _ hQ'
  simp only [Fintype.card_fin] at h1 h2
  exact ⟨h1, h2⟩

theorem sig_sum (S : HSpace E) (hS : S.SigOK) (τ : E →+* ℂ) : (S.sig τ).1 + (S.sig τ).2 = S.rank := bridge_sigRank_holds E S hS τ

variable (R : Ranks) (F : Type) [Field F] [NumberField F] [Algebra F E]

theorem baseSpace_posDef : BaseSpacePosDef R F E := by
  intro S τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := S.cm.cmUnram.2.1 τ
  have hXr : (S.X 0).rank = R.k := by rw [S.X_rank 0 (Nat.zero_le _)]; simp [Ranks.N]
  rcases S.X_def 0 (Nat.zero_le _) τ with h | h
  · exact h
  · exfalso
    have hw : (Matrix.of fun i j => (S.Y 0).hT (S.iXY 0 ((S.X 0).frame i))
        (S.iXY 0 ((S.X 0).frame j))) = (S.X 0).gram := by
      ext i j
      exact S.iXY_isom 0 (by have := R.two_le_m; omega) _ _
    have hsX := S.X_sig 0 τ
    rw [h, ← hw] at hsX
    have hsY := S.Y_sig 0 τ
    rw [S.baseSpace_signature_eq τ] at hsY
    have key := (sig_family (S.Y 0) τ hτ _ hsX hsY).2
    rw [S.Y_rank 0 (Nat.zero_le _), hXr] at key
    simp only [Ranks.sigY0, Ranks.rankY, zero_mul, add_zero] at key
    have h1 := R.rS_two
    have h2 := R.r_eq
    have h3 := R.m_add_three_le_k
    omega

theorem factXmDef : FactXmDef R F E := by
  intro S
  have hXr : (S.X R.m).rank = R.N R.m := S.X_rank R.m le_rfl
  have hX'r : S.X'.rank = R.rankX' := S.X'_rank
  have hYr : (S.Y R.m).rank = R.rankX' := by rw [S.Y_rank R.m le_rfl]; rfl
  have hpos : 0 < R.rankX' := by unfold Ranks.rankX' Ranks.r; have := R.k_ge; omega
  have hNX : R.N R.m = R.rankX' + 1 := factXm R
  have hw : (Matrix.of fun i j => (S.X R.m).hT (S.iX' (S.X'.frame i)) (S.iX' (S.X'.frame j))) =
      S.X'.gram := by
    ext i j; exact S.iX'_isom _ _
  have hw2 : (Matrix.of fun i j => (S.Y R.m).hT (S.eYm (S.X'.frame i)) (S.eYm (S.X'.frame j))) =
      S.X'.gram := by
    ext i j; exact S.eYm_isom _ _
  have hs' : ∀ τ, (S.X'.sig τ).1 + (S.X'.sig τ).2 = R.rankX' := fun τ => by
    rw [sig_sum _ S.X'_sig τ, hX'r]
  have key : ∀ τ : E →+* ℂ, ((S.X R.m).sig τ = (R.N R.m, 0) → S.X'.sig τ = (R.rankX', 0)) ∧
      ((S.X R.m).sig τ = (0, R.N R.m) → S.X'.sig τ = (0, R.rankX')) := by
    intro τ
    have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := S.cm.cmUnram.2.1 τ
    have hsX' := S.X'_sig τ
    rw [← hw] at hsX'
    have h3 := hs' τ
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hsX := S.X_sig R.m τ
      rw [h] at hsX
      have k1 := (sig_family (S.X R.m) τ hτ _ hsX' hsX).2
      rw [hXr] at k1
      simp only at k1
      exact Prod.ext (by simp only; omega) (by simp only; omega)
    · have hsX := S.X_sig R.m τ
      rw [h] at hsX
      have k1 := (sig_family (S.X R.m) τ hτ _ hsX' hsX).1
      rw [hXr] at k1
      simp only at k1
      exact Prod.ext (by simp only; omega) (by simp only; omega)
  have keyY : ∀ τ : E →+* ℂ, (S.Y R.m).sig τ = S.X'.sig τ := by
    intro τ
    have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := S.cm.cmUnram.2.1 τ
    have hsX' := S.X'_sig τ
    rw [← hw2] at hsX'
    have k := sig_family (S.Y R.m) τ hτ _ hsX' (S.Y_sig R.m τ)
    have h3 := hs' τ
    have h4 := sig_sum _ (S.Y_sig R.m) τ
    rw [hYr] at k h4
    exact Prod.ext (by omega) (by omega)
  have hX'def : S.X'.IsDefinite := by
    intro τ
    rw [hX'r]
    rcases S.X_def R.m le_rfl τ with h | h
    · rw [hXr] at h; exact Or.inl ((key τ).1 h)
    · rw [hXr] at h; exact Or.inr ((key τ).2 h)
  refine ⟨hX'def, fun τ => ?_, fun τ => ?_⟩
  · rw [keyY τ, hYr, ← hX'r]; exact hX'def τ
  · constructor
    · exact (key τ).1
    · intro h
      rcases S.X_def R.m le_rfl τ with h' | h'
      · rwa [hXr] at h'
      · rw [hXr] at h'
        have := (key τ).2 h'
        rw [h] at this
        simp only [Prod.mk.injEq] at this
        omega

theorem factVSig : FactVSig R F E := by
  intro S j hj1 hj2 τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := S.cm.cmUnram.2.1 τ
  obtain ⟨e, -, -, -, horth⟩ := S.V_std j hj1 hj2
  have hr : (S.V j).rank = R.nV := S.V_rank j hj1 hj2
  have hs := S.V_sig j τ
  have hsum := sig_sum _ (S.V_sig j) τ
  rw [hr] at hsum
  by_cases hneg : S.Vneg j
  · have hw : (Matrix.of fun a b => (S.V j).hT (e a) (e b)) = -1 := by
      ext a b
      have := horth a b
      rw [if_pos hneg] at this
      simp only [LinearMap.neg_apply] at this
      rw [Matrix.of_apply, Matrix.neg_apply, Matrix.one_apply, ← this, neg_neg]
    have hsig : Formalism.UG.HasSignature ((Matrix.of fun a b => (S.V j).hT (e a) (e b)).map τ) 0 R.nV := by
      rw [hw]
      have h0 : (-1 : Matrix (Fin R.nV) (Fin R.nV) E).map τ = -1 := by
        ext a b; by_cases hab : a = b <;> simp [hab]
      rw [h0]
      simpa using Formalism.UG.P.stdform_sig_neg_one (n := Fin R.nV)
    have k := (sig_family (S.V j) τ hτ e hsig hs).2
    rw [hr] at k
    rw [if_pos hneg]
    exact Prod.ext (by simp only; omega) (by simp only; omega)
  · have hw : (Matrix.of fun a b => (S.V j).hT (e a) (e b)) = 1 := by
      ext a b
      have := horth a b
      rw [if_neg hneg] at this
      rw [Matrix.of_apply, Matrix.one_apply, this]
    have hsig : Formalism.UG.HasSignature ((Matrix.of fun a b => (S.V j).hT (e a) (e b)).map τ) R.nV 0 := by
      rw [hw]
      have h0 : (1 : Matrix (Fin R.nV) (Fin R.nV) E).map τ = 1 := by
        ext a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
      rw [h0]
      simpa using Formalism.UG.P.stdform_sig_one (n := Fin R.nV)
    have k := (sig_family (S.V j) τ hτ e hsig hs).1
    rw [hr] at k
    rw [if_neg hneg]
    exact Prod.ext (by simp only; omega) (by simp only; omega)

end sig

namespace Rows

end Rows

theorem factLpF : FactLpF := by
  intro l d _ Ds hl hD
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hSD : 0 ≤ ∑ s, Ds s := Finset.sum_nonneg fun s _ => hD s
  have hbound : ∀ y ∈ lpFeasible l d Ds, y ≤ (l : ℝ) / ((l : ℝ) ^ 2 - 1) * ∑ s, Ds s := by
    rintro y ⟨xs, hx0, hodd, hcon, rfl⟩
    have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hcon s
    rw [Finset.sum_add_distrib] at hsum
    have hshift : ∑ s, ∑ i ∈ Finset.range d, xs (s - (i : ZMod d)) i =
        ∑ s, ∑ i ∈ Finset.range d, xs s i := by
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ (fun s => rfl)
    have hfirst : (l : ℝ) * ∑ s, ∑ i ∈ Finset.range d, xs s i ≤
        ∑ s, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * xs s i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases ho : Odd i
      · have hli : (l : ℝ) ≤ (l : ℝ) ^ i := by
          obtain ⟨k, rfl⟩ := ho
          calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ (l : ℝ) ^ (2 * k + 1) := pow_le_pow_right₀ (by linarith) (by omega)
        exact mul_le_mul_of_nonneg_right hli (hx0 s i)
      · rw [hodd s i (Or.inl ho)]
        simp
    rw [hshift] at hsum
    have hY0 : 0 ≤ ∑ s, ∑ i ∈ Finset.range d, xs s i :=
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => hx0 s i
    have hden : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith
  have h0 : (0 : ℝ) ∈ lpFeasible l d Ds :=
    ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ _ _ => rfl, fun s => by simp [hD s], by simp⟩
  have hbdd : BddAbove (lpFeasible l d Ds) := ⟨_, hbound⟩
  unfold lpF
  constructor
  · have := csSup_le ⟨0, h0⟩ hbound
    linarith
  · have := le_csSup hbdd h0
    linarith

theorem detPow_mul (R : Type) [CommRing R] (N : ℕ) (g h : GL (Fin N) R) (c : ℤ) :
    detPow R N (g * h) c = detPow R N g c * detPow R N h c := by
  simp only [detPow, map_mul, mul_zpow, Units.val_mul]

theorem rowAct_tr_eq (R : Type) [CommRing R] (N : ℕ) (g : GL (Fin N) R)
    (f : MvPolynomial (Fin N × Fin N) R) :
    Formalism.GradedWeylDivisibility.rowAct R (n := N) (g : Matrix (Fin N) (Fin N) R).transpose f =
      Formalism.UG.dwAct R N N (inside₂ R N g) f := rfl

theorem invTr_mul (R : Type) [CommRing R] (N : ℕ) (g h : GL (Fin N) R) :
    inside₂ R N (g * h) = inside₂ R N g * inside₂ R N h := by
  apply Units.ext
  show ((g * h)⁻¹ : GL (Fin N) R).val.transpose = ((g⁻¹ : GL (Fin N) R).val.transpose) * ((h⁻¹ : GL (Fin N) R).val.transpose)
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem bridge_round_square_holds : bridge_round_square := by
  intro R _ N lam g f
  simp only [roundAct, sqAct]
  have h1 : inside₂ R N (inside₂ R N g) = g := by
    apply Units.ext
    show (g : Matrix (Fin N) (Fin N) R).transpose.transpose = (g : Matrix (Fin N) (Fin N) R)
    exact Matrix.transpose_transpose _
  have h3 : Matrix.GeneralLinearGroup.det (inside₂ R N g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
    rw [← map_inv]
    apply Units.ext
    show ((g⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R).transpose.det = ((g⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R).det
    exact Matrix.det_transpose _
  have h2 : detPow R N (inside₂ R N g) lam.detShift = detPow R N g (-lam.detShift) := by
    simp only [detPow, h3, inv_zpow']
  rw [rowAct_tr_eq, h1, h2]

theorem factSqActMul : FactSqActMul := by
  intro R _ N lam g h f
  have hmul := Formalism.UG.Final.DwActMul R N N
  refine ⟨?_, ?_⟩
  · unfold sqAct
    rw [rowAct_tr_eq, rowAct_tr_eq, rowAct_tr_eq, invTr_mul, (hmul _ _).1, AlgHom.comp_apply,
      map_smul, smul_smul, detPow_mul]
  · unfold roundAct
    rw [(hmul g h).1, AlgHom.comp_apply, map_smul, smul_smul, detPow_mul]

theorem factSqStable : FactSqStable := by
  intro R _ N lam g
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩
  · unfold sqAct
    exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable R N N _ _ f hf)
  · unfold sqAct
    rw [rowAct_tr_eq]
    exact Submodule.smul_mem _ _ (Formalism.UG.Final.WeylGLStable R N N le_rfl _ _ f hf)

theorem bridge_normFock_extremal_holds : bridge_normFock_extremal := by
  intro N lam
  unfold normFock
  have hne : extremal ℂ N lam ≠ 0 := Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW
  have hpos := Formalism.GradedWeylDivisibility.fockPos _ (extremal ℂ N lam) hne
  have h0 : Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam) ≠ 0 := by
    intro h; rw [h] at hpos; simp at hpos
  exact div_self h0

theorem nPl_two_mul (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] :
    (Formalism.HN.nPl K : ℝ) * 2 = Module.finrank ℚ K := by
  simp only [Formalism.HN.nPl]
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
  have h3 : NumberField.InfinitePlace.nrRealPlaces K = 0 := by
    first
    | exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero K
    | exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero (K := K)
    | exact (NumberField.IsTotallyComplex.nrRealPlaces_eq_zero (K := K)).1
    | simp
    | (simp only [NumberField.InfinitePlace.nrRealPlaces, Fintype.card_eq_zero_iff]
       exact ⟨fun w => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (NumberField.IsTotallyComplex.isComplex w.1)) w.2⟩)
  exact_mod_cast (by omega : Fintype.card (NumberField.InfinitePlace K) * 2 = Module.finrank ℚ K)

theorem HLat.L_ne_bot {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)
    (hr : 0 < A.rank) : A.L ≠ ⊥ := by
  intro h
  have h1 : Submodule.span K ((A.L : Set A.V)) = ⊥ := by
    rw [h, Submodule.bot_coe, Submodule.span_zero_singleton]
  have h2 : A.rank = 0 := by
    show Module.finrank K (Submodule.span K ((A.L : Set A.V))) = 0
    rw [h1, finrank_bot]
  omega

theorem bridge_hn_mu_holds : bridge_hn_mu := by
  intro K _ _ _ _ A hG hr
  have hL := A.L_ne_bot hr
  have hsz := Formalism.HN.sizeMu K A.V A.ι A.b A.X hG.1 A.L hG.2.1 hL
  have hht := (Formalism.HN.plLat K A.V A.ι A.b A.X hG.1 A.L hG.2.1).2.2
  simp only at hsz
  have hn := nPl_two_mul K
  have hrk : (0 : ℝ) < A.rank := by exact_mod_cast hr
  have hnp : (0 : ℝ) < Formalism.HN.nPl K := by
    have : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    linarith
  unfold HLat.mu HLat.lcv
  rw [hsz.2.1]
  unfold Formalism.HN.size
  rw [Real.log_rpow hht, ← hn]
  simp only [HLat.rank] at hrk ⊢
  field_simp

theorem bridge_dual_mu_holds : bridge_dual_mu := by
  intro K _ _ _ _ A hG hr
  have hL := A.L_ne_bot hr
  have hd := Formalism.HN.dualPl K A.V A.ι A.b A.X hG.1 A.L hG.2.1 hG.2.2
  have hXd : ∀ v, IsUnit (Formalism.HN.dualFrame A.X v).det := fun v =>
    Matrix.isUnit_nonsing_inv_det _ (by rw [Matrix.det_transpose]; exact hG.1 v)
  have : Module.Finite K A.V := Module.Finite.of_basis A.b
  have hdne : Formalism.HN.dualLat A.L ≠ ⊥ := by
    intro h
    have htop := hd.2.1
    rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at htop
    have h0 : Module.finrank K (Module.Dual K A.V) = 0 := by
      rw [← finrank_top K (Module.Dual K A.V), ← htop, finrank_bot]
    rw [Subspace.dual_finrank_eq] at h0
    have : Formalism.HN.rkK A.L ≤ Module.finrank K A.V := Submodule.finrank_le _
    simp only [HLat.rank] at hr
    omega
  have hs1 := Formalism.HN.sizeMu K A.V A.ι A.b A.X hG.1 A.L hG.2.1 hL
  have hs2 := Formalism.HN.sizeMu K (Module.Dual K A.V) A.ι A.b.dualBasis (Formalism.HN.dualFrame A.X) hXd
    (Formalism.HN.dualLat A.L) hd.1 hdne
  simp only at hs1 hs2
  have e := hd.2.2.2.2.2.1
  rw [hs2.2.2.2.2.1, hs1.2.2.2.1, ← Real.exp_neg] at e
  have e2 := Real.exp_injective e
  unfold HLat.muMinDual HLat.muMax HLat.dualB HLat.dualX HLat.dualL Formalism.HN.muMinDef Formalism.HN.muMaxDef
  have hc : Formalism.HN.logDisc K / (2 * (Module.finrank ℚ K : ℝ)) =
      Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ) / 2 := by rw [div_div, mul_comm]
  rw [hc] at e2
  linarith

section places

variable {K : Type} [Field K] [NumberField K]

theorem span_prime_isMaximal (p : ℕ) (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal := by
  haveI := Fact.mk hp
  exact Int.ideal_span_isMaximal_of_prime p

theorem liesOver_of_mem (p : ℕ) (hp : p.Prime) (w : HeightOneSpectrum (𝓞 K))
    (hmem : (p : 𝓞 K) ∈ w.asIdeal) : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hmax := span_prime_isMaximal p hp
  have hP : (w.asIdeal.comap (algebraMap ℤ (𝓞 K))).IsPrime := w.isPrime.comap _
  have hle : Ideal.span {(p : ℤ)} ≤ w.asIdeal.comap (algebraMap ℤ (𝓞 K)) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hmem
  exact ⟨hmax.eq_of_le hP.ne_top hle⟩

theorem mem_of_liesOver (p : ℕ) (q : Ideal (𝓞 K)) [q.LiesOver (Ideal.span {(p : ℤ)})] :
    (p : 𝓞 K) ∈ q := by
  have h : Ideal.span {(p : ℤ)} = q.under ℤ := Ideal.LiesOver.over
  have hm : (p : ℤ) ∈ q.under ℤ := by
    rw [← h]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hm2 : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ q := hm
  simpa using hm2

theorem sum_e_f (p : ℕ) (hp : p.Prime) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ w, w ∈ S ↔ (p : 𝓞 K) ∈ w.asIdeal) :
    ∑ w ∈ S, eWL K w * w.asIdeal.inertiaDeg ℤ = Module.finrank ℚ K := by
  have := span_prime_isMaximal p hp
  have hP0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simp [hp.ne_zero]
  have h := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [NumberField.RingOfIntegers.rank] at h
  rw [← h]
  refine Finset.sum_bij' (fun w hw => ⟨w.asIdeal, w.isPrime, liesOver_of_mem p hp w ((hS w).mp hw)⟩)
    (fun q _ => ⟨q.1, q.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot hP0 q.1⟩)
    (fun _ _ => Finset.mem_univ _) (fun q _ => ?_) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)
  rw [hS]
  have := q.2.2
  exact mem_of_liesOver p q.1

theorem sum_lw_e (p : ℕ) (hp : p.Prime) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ w, w ∈ S ↔ (p : 𝓞 K) ∈ w.asIdeal) :
    ∑ w ∈ S, lw K w * (eWL K w : ℝ) = Real.log p := by
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hterm : ∀ w ∈ S, lw K w * (eWL K w : ℝ) =
      Real.log p / Module.finrank ℚ K * ((eWL K w * w.asIdeal.inertiaDeg ℤ : ℕ) : ℝ) := by
    intro w hw
    have := liesOver_of_mem p hp w ((hS w).mp hw)
    have hN := Ideal.pow_inertiaDeg p w.asIdeal
    unfold lw
    rw [← hN]
    push_cast
    rw [Real.log_pow]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have := sum_e_f p hp S hS
  rw [← Nat.cast_sum, this]
  field_simp

theorem finite_places_over (p : ℕ) (hp : p.Prime) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ w, w ∈ S ↔ (p : 𝓞 K) ∈ w.asIdeal := by
  have hI : Ideal.span {(p : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hfin := Ideal.finite_factors hI
  refine ⟨hfin.toFinset, fun w => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]

end places

theorem resChar_mem (D : D7) (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have hv := D.what₂.places.val_resChar w
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := by
    exact_mod_cast (D.what₂.places.resChar_prime w).ne_zero
  rw [D.val_eq w _ hne] at hv
  have hv' : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) =
      ((D.what₂.places.ramIdx w : ℕ) : ℤ) := by exact_mod_cast hv
  have hpos := D.what₂.places.ramIdx_pos w
  have h1 : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL
      ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) < 1 := by
    have hx : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = algebraMap (𝓞 D.what₂.LL) D.what₂.LL
        ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) := by simp
    rw [← hx]
    have hv0 : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr hne
    unfold vAdd at hv'
    rw [← WithZero.exp_log hv0, show WithZero.log ((D.plEq w).valuation D.what₂.LL
      ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)) = -((D.what₂.places.ramIdx w : ℕ) : ℤ) by omega]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  exact ((D.plEq w).valuation_lt_one_iff_mem _).mp h1

theorem factEtaMean : FactEtaMean := by
  intro D _ l hl S hS
  classical
  have hiff : ∀ w, D.what₂.places.resChar w = l ↔ (l : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
    intro w
    constructor
    · intro h; rw [← h]; exact resChar_mem D w
    · intro hmem
      by_contra hne
      have h1 := resChar_mem D w
      have hcop : Nat.Coprime (D.what₂.places.resChar w) l :=
        (Nat.coprime_primes (D.what₂.places.resChar_prime w) hl).mpr hne
      obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (D.what₂.places.resChar w : ℤ) + b * (l : ℤ) = 1 := by
        refine ⟨Nat.gcdA (D.what₂.places.resChar w) l, Nat.gcdB (D.what₂.places.resChar w) l, ?_⟩
        have := Nat.gcd_eq_gcd_ab (D.what₂.places.resChar w) l
        rw [hcop] at this
        push_cast at this
        linarith
      have h1' : (1 : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
        have : ((a * (D.what₂.places.resChar w : ℤ) + b * (l : ℤ) : ℤ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
          push_cast
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hmem)
        rwa [hab, Int.cast_one] at this
      exact (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1')
  have hS' : ∀ v, v ∈ S.map D.plEq.toEmbedding ↔ (l : 𝓞 D.what₂.LL) ∈ v.asIdeal := by
    intro v
    rw [Finset.mem_map_equiv, hS, hiff, Equiv.apply_symm_apply]
  rw [← sum_lw_e l hl _ hS', Finset.sum_map]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [D.ram_eq w]

section hw

open MvPolynomial

theorem rowAct_lpMinor (R : Type) [CommRing R] (N s : ℕ) (hs hs' : s ≤ N)
    (A : Matrix (Fin N) (Fin N) R) (hA : ∀ i j, i < j → A i j = 0) (hA1 : ∀ i, A i i = 1) :
    Formalism.GradedWeylDivisibility.rowAct R (n := N) A (Formalism.GradedWeylDivisibility.lpMinor R s hs hs') = Formalism.GradedWeylDivisibility.lpMinor R s hs hs' := by
  unfold Formalism.GradedWeylDivisibility.lpMinor
  rw [AlgHom.map_det]
  have hmat : (Formalism.GradedWeylDivisibility.rowAct R (n := N) A).mapMatrix
      (Matrix.of fun p q : Fin s =>
        (X (Fin.castLE hs p, Fin.castLE hs' q) : MvPolynomial (Fin N × Fin N) R)) =
      (Matrix.of fun p c : Fin s =>
        (C (A (Fin.castLE hs p) (Fin.castLE hs c)) : MvPolynomial (Fin N × Fin N) R)) *
      (Matrix.of fun p q : Fin s =>
        (X (Fin.castLE hs p, Fin.castLE hs' q) : MvPolynomial (Fin N × Fin N) R)) := by
    apply Matrix.ext
    intro p q
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Formalism.GradedWeylDivisibility.rowAct, aeval_X,
      Matrix.mul_apply]
    have e1 : ∑ c : Fin s, (C (A (Fin.castLE hs p) (Fin.castLE hs c)) *
          X (Fin.castLE hs c, Fin.castLE hs' q) : MvPolynomial (Fin N × Fin N) R) =
        ∑ b ∈ Finset.univ.map (Fin.castLEEmb hs), (C (A (Fin.castLE hs p) b) *
          X (b, Fin.castLE hs' q) : MvPolynomial (Fin N × Fin N) R) := by
      rw [Finset.sum_map]; rfl
    rw [e1]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro b _ hb
    have hsb : s ≤ b.val := by
      by_contra hlt
      push Not at hlt
      exact hb (Finset.mem_map.mpr ⟨⟨b.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    have hlt : Fin.castLE hs p < b := by
      rw [Fin.lt_def]; simp only [Fin.val_castLE]; omega
    rw [hA _ _ hlt]
    simp
  rw [hmat, Matrix.det_mul]
  have hdetA : (Matrix.of fun p c : Fin s =>
      (C (A (Fin.castLE hs p) (Fin.castLE hs c)) : MvPolynomial (Fin N × Fin N) R)).det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · simp [hA1]
    · intro i j hij
      have hij' : i < j := hij
      rw [Matrix.of_apply, hA _ _ (by rw [Fin.lt_def] at hij' ⊢; simpa using hij')]
      simp
  rw [hdetA, one_mul]

theorem factSqHighestWeight : FactSqHighestWeight := by
  intro R _ N lam
  have hN := factNatW N lam
  refine ⟨fun t => ?_, fun g hg h1 => ?_⟩
  · unfold sqAct extremal
    have hdiag : ((diagGL R N t : GL (Fin N) R) : Matrix (Fin N) (Fin N) R).transpose =
        Matrix.diagonal fun a => (t a : R) := by
      show (Matrix.diagonal fun a => (t a : R)).transpose = _
      exact Matrix.diagonal_transpose _
    rw [hdiag, Formalism.GradedWeylDivisibility.rowActDiagWeight R N N (fun a => (t a : R)) _ _
      (Formalism.GradedWeylDivisibility.hwRowWeight R N N le_rfl lam.natW hN.1), smul_smul]
    congr 1
    have hu : Matrix.GeneralLinearGroup.det (diagGL R N t) = ∏ a, t a := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      show (Matrix.diagonal fun a => (t a : R)).det = _
      rw [Matrix.det_diagonal, Units.coe_prod]
    have hprod : (∏ a, t a ^ lam.w a : Rˣ) =
        (∏ a, t a) ^ lam.detShift * ∏ a, t a ^ (lam.natW a) := by
      rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← hN.2.1 a, add_comm, zpow_add, zpow_natCast]
    rw [hprod, detPow, hu, Units.val_mul, Units.coe_prod]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [Formalism.GradedWeylDivisibility.rowNu]
  · have hdet : Matrix.GeneralLinearGroup.det g = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_upperTriangular hg]
      simp [h1]
    unfold sqAct
    rw [detPow, hdet, one_zpow, Units.val_one, one_smul]
    unfold extremal Formalism.GradedWeylDivisibility.hw
    rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow]
    congr 1
    refine rowAct_lpMinor R N _ _ _ _ (fun i j hij => ?_) (fun i => ?_)
    · rw [Matrix.transpose_apply]; exact hg hij
    · rw [Matrix.transpose_apply]; exact h1 i

theorem factDelDualNabla_of (h : Formalism.GradedWeylDivisibility.WeylEqDualNabla) : FactDelDualNabla := by
  intro N lam f hf
  have hN := factNatW N lam
  have hE := h N N le_rfl lam.natW hN.1
  have hne : extremal ℚ N lam ≠ 0 := Formalism.GradedWeylDivisibility.hwNe ℚ N N le_rfl lam.natW
  have hpos : Formalism.GradedWeylDivisibility.fockQ (extremal ℚ N lam) (extremal ℚ N lam) ≠ 0 :=
    ((Formalism.GradedWeylDivisibility.fockQPos _ _ (extremal ℚ N lam)).2 hne).ne'
  have hmem : (∃ f₀ ∈ delSq ℤ N lam, map (Int.castRingHom ℚ) f₀ = f) ↔
      f ∈ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl lam.natW).map (Formalism.GradedWeylDivisibility.intQ N N) := by
    rw [Submodule.mem_map]; rfl
  rw [hmem, hE]
  constructor
  · intro hz
    refine ⟨hf, ?_⟩
    rintro Q ⟨g, hg, rfl⟩
    obtain ⟨z, hz'⟩ := hz g hg
    refine ⟨z, ?_⟩
    unfold normFockQ at hz'
    rw [div_eq_iff hpos] at hz'
    exact hz'
  · rintro ⟨-, hQ⟩ g hg
    obtain ⟨z, hz⟩ := hQ _ (Submodule.mem_map_of_mem hg)
    refine ⟨z, ?_⟩
    unfold normFockQ
    rw [div_eq_iff hpos]
    exact hz

end hw

section principal

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition FractionalIdeal
open scoped Pointwise

def DiffKPrincipal : Prop := ∀ (R : Ranks) (H : Host R),
  (((differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) : Ideal (𝓞 H.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) =
    spanSingleton (nonZeroDivisors (𝓞 H.E)) H.sqrtMinusD

def CcNorm : Prop := ∀ (R : Ranks) (H : Host R),
  ((H.ccE : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) *
    ((H.conj • H.ccE : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) =
    spanSingleton (nonZeroDivisors (𝓞 H.E)) ((Ideal.absNorm H.ccK : ℕ) : H.E)

theorem factPrincipalDatum_of (h1 : DiffKPrincipal) (h2 : CcNorm) : FactPrincipalDatum := by
  intro R H
  have ht : H.ddE = differentIdeal (𝓞 H.K) (𝓞 H.E) *
      (differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) :=
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 H.K) (𝓞 H.E)
  have hne : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  have hspec : differentIdeal (𝓞 H.K) (𝓞 H.E) = H.𝔟 * (H.conj • H.𝔟) := H.𝔟_spec.1
  rw [hspec] at hne ht
  have hB : ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 := by
    rw [Ne, coeIdeal_eq_zero]
    rintro h
    exact hne (by rw [h]; simp)
  have hB' : ((H.conj • H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 := by
    rw [Ne, coeIdeal_eq_zero]
    rintro h
    exact hne (by rw [h]; simp)
  have hN : ((Ideal.absNorm H.ccK : ℕ) : H.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact H.ccK_ne_bot
  have hd : H.sqrtMinusD ≠ 0 := H.sqd_ne_zero
  rw [ht, coeIdeal_mul, coeIdeal_mul, h1 R H]
  unfold Host.AA Host.AAbar Host.AA0
  have hcalc : ∀ (s C C' B B' D : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E),
      s * (C * B⁻¹) * (C' * B'⁻¹) * (B * B' * D) = s * (C * C') * D * (B⁻¹ * B) * (B'⁻¹ * B') := by
    intro s C C' B B' D
    ring
  rw [hcalc, inv_mul_cancel₀ hB, inv_mul_cancel₀ hB', h2 R H, mul_one, mul_one,
    spanSingleton_mul_spanSingleton, spanSingleton_mul_spanSingleton]
  have hval : H.xi0 * ((Ideal.absNorm H.ccK : ℕ) : H.E) * H.sqrtMinusD = -1 := by
    unfold Host.xi0
    field_simp
  rw [hval, ← spanSingleton_one, spanSingleton_eq_spanSingleton]
  exact ⟨-1, by simp⟩

end principal

end Formalism.BasicNotions

end
