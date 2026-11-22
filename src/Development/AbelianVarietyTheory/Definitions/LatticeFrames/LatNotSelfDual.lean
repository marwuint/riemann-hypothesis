import Mathlib
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexIteratedLevelChainInFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetricPositionLevelShapeOnParabolic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnifUnit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colChar)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LevelTest

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {ι : Type} (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

theorem val_lt_one_iff {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt q.e PP) (x : 𝓞 D.host.E) :
    valuation K (q.pr (incA D (x : D.host.E))) < 1 ↔ x ∈ PP.asIdeal := by
  by_cases hx : x = 0
  · subst hx; simp
  have h0 : (q.pr.comp (incA D)) (x : D.host.E) ≠ 0 := (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
  rw [h.2 x hx, ← q.sec_pr, ← q.int_iff]
  change valuation K ((q.pr.comp (incA D)) x) < 1 ↔ ¬ valuation K ((q.pr.comp (incA D)) (x : D.host.E)⁻¹) ≤ 1
  rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]

section Unif

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E}

theorem val_le_one (x : 𝓞 D.host.E) : valuation K (q.pr (incA D (x : D.host.E))) ≤ 1 := by
  have := GlobalTheory.FinPl.SplitApprox.val_le q 1 one_pos (incA D (x : D.host.E)) (finPart D (incA D (x : D.host.E)))
    (GlobalTheory.FinPl.SplitApprox.tmul_mem (a := 1) (fun v => by rw [map_one]; exact one_mem _) x.2) (by simp)
  simpa using this

theorem val_le_one_of (h : Formalism.L2.NTheta.IsIdemAt q.e PP) {y : D.host.E} (hy : PP.valuation D.host.E y ≤ 1) :
    valuation K (q.pr (incA D y)) ≤ 1 := by
  obtain ⟨n, d, e⟩ := PP.exists_primeCompl_mul_eq_of_integer y hy
  have hd : valuation K (q.pr (incA D ((d : 𝓞 D.host.E) : D.host.E))) = 1 :=
    le_antisymm (val_le_one q _) (not_lt.1 fun h' => d.2 ((val_lt_one_iff q h _).1 h'))
  have := val_le_one q n
  rw [show (n : D.host.E) = y * ((d : 𝓞 D.host.E) : D.host.E) from e.symm, map_mul, map_mul, map_mul, hd, mul_one] at this
  exact this

theorem val_eq_unif (h : Formalism.L2.NTheta.IsIdemAt q.e PP) (ϖ : Unif K) {x : 𝓞 D.host.E} (h1 : x ∈ PP.asIdeal)
    (h2 : x ∉ PP.asIdeal ^ 2) : valuation K (q.pr (incA D (x : D.host.E))) = valuation K ((ϖ.1 : 𝒪[K]) : K) := by
  obtain ⟨c, hc, -⟩ := GlobalTheory.FinPl.SplitApprox.exists_unif_unit D K q ϖ
  have hq := (GlobalTheory.FinPl.SplitApprox.exists_nat ϖ).1
  have hx0 : (x : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 fun h0 => h2 (h0 ▸ zero_mem _)
  refine le_antisymm ?_ ?_
  · have hm : (⟨_, val_le_one q x⟩ : 𝒪[K]) ∈ maximalIdeal 𝒪[K] :=
      Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 ((val_lt_one_iff q h x).2 h1)
    obtain ⟨r, hr⟩ := ϖ.mem_max_iff.1 hm
    have hr' : q.pr (incA D (x : D.host.E)) = ((ϖ.1 : 𝒪[K]) : K) * r := congrArg (fun x : 𝒪[K] => (x : K)) hr
    rw [hr', map_mul]; exact mul_le_of_le_one_right' r.2
  · have hc0 : c ≠ 0 := by
      rintro rfl
      exact ϖ.ne_zero (by simpa using hc.symm)
    have hc1 : PP.valuation D.host.E c < 1 := by
      by_contra hge
      have := val_le_one_of q h (y := c⁻¹) (by rw [map_inv₀]; exact inv_le_one_of_one_le₀ (not_lt.1 hge))
      have h3 : valuation K (q.pr (incA D c)) * valuation K (q.pr (incA D c⁻¹)) = 1 := by
        rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ hc0]; simp
      have h4 : valuation K (q.pr (incA D c)) * valuation K (q.pr (incA D c⁻¹)) < 1 :=
        (mul_le_of_le_one_right' this).trans_lt (hc ▸ hq)
      exact h4.ne h3
    have hx : WithZero.exp (-1 : ℤ) ≤ PP.valuation D.host.E (x : D.host.E) := by
      have h5 : ¬ PP.intValuation x ≤ WithZero.exp (-(2 : ℕ) : ℤ) := fun h' =>
        h2 ((PP.intValuation_le_pow_iff_mem x 2).1 h')
      rw [show (x : D.host.E) = algebraMap _ _ x from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      have hne : PP.intValuation x ≠ 0 := PP.intValuation_ne_zero _ fun h0 => h2 (h0 ▸ zero_mem _)
      rw [← WithZero.exp_log hne, WithZero.exp_le_exp] at h5 ⊢
      omega
    have hc2 : PP.valuation D.host.E c ≤ WithZero.exp (-1 : ℤ) := by
      have hne : PP.valuation D.host.E c ≠ 0 := (map_ne_zero _).2 hc0
      rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hc1
      rw [← WithZero.exp_log hne, WithZero.exp_le_exp]
      omega
    have h6 := val_le_one_of q h (y := c / x) (by
      rw [map_div₀]; exact div_le_one_of_le₀ (hc2.trans hx) zero_le')
    rw [← hc, show c = (x : D.host.E) * (c / x) by field_simp, map_mul, map_mul, map_mul]
    exact mul_le_of_le_one_right' h6

theorem unif_val (ϖ : Unif K) {π : Kˣ} (h : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif π) : valuation K ((ϖ.1 : 𝒪[K]) : K) = valuation K (π : K) := by
  have hq := (GlobalTheory.FinPl.SplitApprox.exists_nat ϖ).1
  refine le_antisymm ((h _).1 hq) ?_
  have h1 := (h _).2 le_rfl
  have hm : (⟨(π : K), h1.le⟩ : 𝒪[K]) ∈ maximalIdeal 𝒪[K] := Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 h1
  obtain ⟨r, hr⟩ := ϖ.mem_max_iff.1 hm
  have hr' : (π : K) = ((ϖ.1 : 𝒪[K]) : K) * r := congrArg (fun x : 𝒪[K] => (x : K)) hr
  rw [hr', map_mul]; exact mul_le_of_le_one_right' r.2

end Unif

theorem exists_prime {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (q : GlobalTheory.FinPl.SplitPt D K) : ∃ PP : Formalism.L2.DIV.Pl D.host.E, Formalism.L2.NTheta.IsIdemAt q.e PP := by
  let φ : 𝓞 D.host.E →+* 𝒪[K] :=
    ((q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict 𝒪[K] fun x => val_le_one q x
  have hφ : ∀ x, x ∈ (maximalIdeal 𝒪[K]).comap φ ↔ valuation K (q.pr (incA D (x : D.host.E))) < 1 := fun x =>
    Valuation.Integer.not_isUnit_iff_valuation_lt_one
  obtain ⟨ϖ⟩ : Nonempty (Unif K) := inferInstance
  obtain ⟨hq, N, hN, hNq⟩ := GlobalTheory.FinPl.SplitApprox.exists_nat ϖ
  refine ⟨⟨(maximalIdeal 𝒪[K]).comap φ, Ideal.comap_isPrime _ _, fun h0 => ?_⟩, q.split, fun x hx => ?_⟩
  · have : (N : 𝓞 D.host.E) ∈ (maximalIdeal 𝒪[K]).comap φ := (hφ _).2 (by simpa using hNq.trans hq)
    rw [h0, Ideal.mem_bot] at this
    exact hN.ne' (by exact_mod_cast this)
  · have h0 : (q.pr.comp (incA D)) (x : D.host.E) ≠ 0 := (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
    refine (hφ x).trans ?_
    rw [← q.sec_pr, ← q.int_iff]
    change valuation K ((q.pr.comp (incA D)) x) < 1 ↔ ¬ valuation K ((q.pr.comp (incA D)) (x : D.host.E)⁻¹) ≤ 1
    rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]

theorem notMem_sq {p : ℕ} (h : GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses.SplitsCompletely D.host.E p) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : (p : 𝓞 D.host.E) ∈ P.asIdeal) : (p : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 := by
  obtain ⟨hp, h⟩ := h
  rw [GlobalTheory.HostSplit.ncard_placesOver _ hp] at h
  haveI := P.isPrime
  exact (GlobalTheory.LocSplit.split_prime hp h P.asIdeal hP).1

theorem unifT_of (p : GlobalTheory.FinPl.SplitPt D k) (ϖ : Unif k) (h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.v.asIdeal) :
    valuation k (p.pr (incA D (((D.mem u).A.T : ℕ) : D.host.E))) = valuation k ((ϖ.1 : 𝒪[k]) : k) := by
  obtain ⟨PP, hPP⟩ := exists_prime p
  obtain ⟨ε, hε, he⟩ := p.above
  have hv := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP _ ε hPP hε he
  have h1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rw [← hv] at h
    simpa using (Ideal.mem_comap.1 h)
  rw [← val_eq_unif p hPP ϖ h1 (notMem_sq (GlobalTheory.ColClassCompare.levelPrime_splitsCompletely_in_cmField D u) PP h1)]
  simp

theorem g_notMem_sq (P : HeightOneSpectrum (𝓞 D.host.E)) : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 := by
  have key : ∀ i j : Fin 2, D.host.g i ≠ D.host.g j → ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      ((D.host.g i : ℕ) : 𝓞 D.host.E) * (D.host.g j : ℕ) ∉ P.asIdeal ^ 2 := fun i j hij hi h => by
    have hc := (Nat.coprime_primes (D.host.g_prime i) (D.host.g_prime j)).2 hij
    obtain ⟨x, y, hxy⟩ := (Nat.Coprime.cast (R := 𝓞 D.host.E) hc)
    refine notMem_sq (GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses.splitsCompletely_g D i) P hi ?_
    have e : ((D.host.g i : ℕ) : 𝓞 D.host.E) = x * (((D.host.g i : ℕ) : 𝓞 D.host.E) * (D.host.g i : ℕ)) +
        y * (((D.host.g i : ℕ) : 𝓞 D.host.E) * (D.host.g j : ℕ)) := by linear_combination (-((D.host.g i : ℕ) : 𝓞 D.host.E)) * hxy
    rw [e]
    exact add_mem (Ideal.mul_mem_left _ _ (by rw [pow_two]; exact Ideal.mul_mem_mul hi hi)) (Ideal.mul_mem_left _ _ h)
  intro h
  rw [Nat.cast_mul] at h
  rcases P.isPrime.mem_or_mem (Ideal.pow_le_self two_ne_zero h) with h0 | h1
  · exact key 0 1 D.host.g_ne h0 h
  · exact key 1 0 D.host.g_ne.symm h1 (by rwa [mul_comm])

theorem comp_map {F E : Type} [Field F] [Field E] [Algebra F E] {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    [CommRing R''] [Algebra F R''] (φ : R →ₐ[F] R') (ψ : R' →ₐ[F] R'') (z : R ⊗[F] E) :
    Algebra.TensorProduct.map (ψ.comp φ) (AlgHom.id F E) z =
      Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) z) := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]

set_option maxHeartbeats 1000000 in

theorem charUnramAt_of {χ : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (h : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w) : CharUnramAt D χ v := by
  have kf : ∀ w (z : AE D), GlobalTheory.AdelicU.compFin D.host.F D.host.E w z = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D z) :=
    fun w z => comp_map _ _ z
  have ki : ∀ w (z : AE D), infPart D z = 1 → GlobalTheory.AdelicU.compInf D.host.F D.host.E w z = 1 := fun w z hz =>
    (comp_map _ _ z).trans ((congrArg (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)) hz).trans
      (map_one _))
  have kint : ∀ y ∈ intAE D, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v y ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := fun y hy => by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy => obtain ⟨α, hα, x, rfl⟩ := hy; exact GlobalTheory.AdelicU.tmul_mem_intLoc (hα v) x
    | zero => rw [RingHom.map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [RingHom.map_add]; exact add_mem hy hz
    | neg y _ hy => rw [RingHom.map_neg]; exact neg_mem hy
  have kin : ∀ z : (AE D)ˣ, finPart D (z : AE D) ∈ intAE D →
      (GlobalTheory.Doubling.unitFin D.host.F D.host.E v z).val ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := fun z hz =>
    Set.mem_of_eq_of_mem (s := GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) (kf v z) (kint _ hz)
  intro x h1 h2 h3 h4
  have hx : x = GlobalTheory.Doubling.ideleAt D.host.F D.host.E v (GlobalTheory.Doubling.unitFin D.host.F D.host.E v x) := by
    refine GlobalTheory.Doubling.idele_ext (fun w => ?_) fun w => ?_
    · rw [GlobalTheory.Doubling.unitInf_ideleAt]
      exact Units.ext (ki w x h1)
    · by_cases hw : w = v
      · subst hw; rw [GlobalTheory.Doubling.unitFin_ideleAt_self]
      · rw [GlobalTheory.Doubling.unitFin_ideleAt_ne hw]
        exact Units.ext ((kf w x).trans (h2 w hw))
  rw [hx]
  refine GlobalTheory.LFun.charAt_eq_one_of_unrAt_datum D χ v _ ?_ ?_ h
  · exact kin x h3
  · rw [← map_inv]
    exact kin x⁻¹ h4

end GlobalTheory.SeeSaw.LevelTest

namespace GlobalTheory.SeeSaw.BaseLatTest

end GlobalTheory.SeeSaw.BaseLatTest

end
