import Mathlib
import Formalism.LocalToGlobal.KernelLattices.MatrixKernelDiamondCommutation
import Formalism.GL3MeanSquares.HookFormulaTorsion.DoubleCosetDecompositionAll
import Formalism.LocalToGlobal.Columns.GSetLemmas
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Columns.RowFormsSel
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.MemGoodPrimesOfNoExceptional
import Formalism.LocalToGlobal.Columns.TiedUpDnA
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.LocalToGlobal.Columns.SmulMemTrpSet
import Formalism.HermitianLattices.HermitianLatticesProofs.NeighbourConstruct

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section FrLoc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

def IsFrAt (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (N : Submodule (𝓞 E) (Sp E n)) (f : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P

theorem single_mem_stdAt {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (s : Fin n) : (Pi.single s (1 : E) : Sp E n) ∈ stdAt E n P := by
  unfold stdAt
  rw [mem_localization_standardLattice]
  intro i
  by_cases h : i = s
  · subst h
    rw [Pi.single_eq_same]
    simpa using IntAt.coe P (1 : 𝓞 E)
  · rw [Pi.single_eq_of_ne h]
    simpa using IntAt.coe P (0 : 𝓞 E)

omit [NumberField E] [StarRing E] in
theorem inFr_add (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x y : HomE E a b) : inFr f f' (x + y) = inFr f f' x + inFr f f' y := by
  unfold inFr
  ext v
  simp

end FrLoc

section FrProd

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] {a b : ℕ}

theorem intAt_natCast (P : HeightOneSpectrum (𝓞 E)) (k : ℕ) : IntAt P (k : E) := by
  simpa using IntAt.coe P (k : 𝓞 E)

end FrProd

section OffAdmCh

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) {u : Pr.Word}

open Classical in

theorem frsF_isFr {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) : IsFrAt P.1 p.deco.1.N (frsF sel mu p P) := by
  unfold frsF
  by_cases h : P.1 ∈ Pr.vGs
  · rw [dif_pos h]
    exact (Deco.liftFr_spec (p.deco.2.hasLift ⟨P.1, h⟩)).1
  · rw [dif_neg h]
    exact p.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩

end OffAdmCh

section MuMoveP

variable {X : Fields} {n : ℕ}

theorem sel_injective {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} (hsel : IsSel X sel) : Function.Injective sel := by
  intro v v' h
  apply HeightOneSpectrum.ext
  rw [← hsel v, ← hsel v', h]

open Classical in

def muFac (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (v : HeightOneSpectrum (𝓞 X.F)) : X.K :=
  if ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal then 1 else ((mU (sel v) ^ ordDet (sel v) N : X.Kˣ) : X.K)

theorem muOff_eq (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (N : Submodule (𝓞 X.E) (Sp X.E n)) : muOff sel SB mU N = ∏ᶠ v, muFac sel SB mU N v := rfl

theorem muFac_support {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} (hsel : IsSel X sel) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (hfin : OrdDetFin X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)) (hN : IsSdLat N) :
    (Function.mulSupport (muFac sel SB mU N)).Finite := by
  refine Set.Finite.subset (Set.Finite.preimage (sel_injective hsel).injOn (hfin N hN)) ?_
  intro v hv
  by_contra hc
  apply hv
  have h0 : ordDet (sel v) N = 0 := by
    by_contra h
    exact hc h
  unfold muFac
  split_ifs
  · rfl
  · rw [h0]
    simp

end MuMoveP

section OrdFin

variable {E : Type} [Field E] [NumberField E]

theorem val_le_one_of_intAt {Q : HeightOneSpectrum (𝓞 E)} {a : E} (h : IntAt Q a) : Q.valuation E a ≤ 1 := by
  obtain ⟨r, s, hs, hrs⟩ := h
  have h1 : Q.valuation E (algebraMap (𝓞 E) E s) = 1 :=
    le_antisymm (Q.valuation_le_one s) (not_lt.1 fun hlt => hs ((Q.valuation_lt_one_iff_mem s).1 hlt))
  have h2 := congrArg (Q.valuation E) hrs
  rw [map_mul, h1, one_mul] at h2
  rw [h2]
  exact Q.valuation_le_one r

theorem ordE_eq_zero {Q : HeightOneSpectrum (𝓞 E)} {a : E} (ha : a ≠ 0) (h : IntAt Q a) (h' : IntAt Q a⁻¹) : ordE Q a = 0 := by
  have h1 := val_le_one_of_intAt h
  have h2 := val_le_one_of_intAt h'
  rw [map_inv₀] at h2
  have h0 : 0 < Q.valuation E a := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha)
  have h3 : Q.valuation E a = 1 := le_antisymm h1 ((inv_le_one₀ h0).1 h2)
  unfold ordE
  rw [h3, WithZero.log_one, neg_zero]

variable [StarRing E]

theorem frame_det_unit_almost_all_primes (n : ℕ) : OrdDetFin E n := by
  intro N hN
  obtain ⟨a, ha0, ha⟩ := exists_smul_le N (stdLat E n) hN.1.fg (stdLat_lattice (E := E) (n := n)).span_eq_top
  obtain ⟨a', ha0', ha'⟩ := exists_smul_le (stdLat E n) N (stdLat_lattice (E := E) (n := n)).fg hN.1.span_eq_top
  have hI : Ideal.span {a * a'} ≠ (0 : Ideal (𝓞 E)) := by
    intro h0
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h0
    exact (mul_ne_zero ha0 ha0') h0
  refine (Ideal.finite_factors hI).subset ?_
  intro Q hQ
  by_contra hc
  apply hQ
  have hm : a * a' ∉ Q.asIdeal := fun hmem => hc (Ideal.dvd_span_singleton.2 hmem)
  have haQ : a ∉ Q.asIdeal := fun hmem => hm (Ideal.mul_mem_right _ _ hmem)
  have haQ' : a' ∉ Q.asIdeal := fun hmem => hm (Ideal.mul_mem_left _ _ hmem)
  have hloc : localization₂ Q.asIdeal N = stdAt E n Q := SameAt.localization_eq ⟨a, haQ, a', haQ', ha, ha'⟩
  have hspec : ∀ x, frameAt Q N x ∈ localization₂ Q.asIdeal N ↔ x ∈ stdAt E n Q :=
    Classical.epsilon_spec (p := fun f : Sp E n ≃ₗ[E] Sp E n => ∀ x, f x ∈ localization₂ Q.asIdeal N ↔ x ∈ stdAt E n Q)
      ⟨1, fun x => by rw [hloc]; rfl⟩
  have hG : frameAt Q N ∈ GLint E n Q := fun x => by
    have := hspec x
    rw [hloc] at this
    exact this
  exact ordE_eq_zero (Units.ne_zero _) (intAt_det _ hG) (intAt_det_inv _ hG)

end OrdFin

section OrdWD

variable {E : Type} [Field E] [NumberField E]

theorem ordE_mul (Q : HeightOneSpectrum (𝓞 E)) {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) : ordE Q (a * b) = ordE Q a + ordE Q b := by
  unfold ordE
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb)]
  ring

variable [StarRing E]

theorem ordDet_eq_of_frame {n : ℕ} (Q : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (f : Sp E n ≃ₗ[E] Sp E n)
    (hf : ∀ x, f x ∈ localization₂ Q.asIdeal N ↔ x ∈ stdAt E n Q) : ordDet Q N = ordE Q ((LinearEquiv.det f : Eˣ) : E) := by
  have hspec : ∀ x, frameAt Q N x ∈ localization₂ Q.asIdeal N ↔ x ∈ stdAt E n Q :=
    Classical.epsilon_spec (p := fun f : Sp E n ≃ₗ[E] Sp E n => ∀ x, f x ∈ localization₂ Q.asIdeal N ↔ x ∈ stdAt E n Q) ⟨f, hf⟩
  have hG : f⁻¹ * frameAt Q N ∈ GLint E n Q := fun x => by
    rw [← hf]
    show f (f.symm (frameAt Q N x)) ∈ _ ↔ _
    rw [LinearEquiv.apply_symm_apply]
    exact hspec x
  have e : frameAt Q N = f * (f⁻¹ * frameAt Q N) := by rw [mul_inv_cancel_left]
  unfold ordDet
  rw [e, map_mul, Units.val_mul, ordE_mul Q (Units.ne_zero _) (Units.ne_zero _),
    ordE_eq_zero (Units.ne_zero _) (intAt_det _ hG) (intAt_det_inv _ hG), add_zero]

end OrdWD

section RedRing

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_negB {a : E} (h : IntAt P a) : IntAt P (-a) := by
  have := (IntAt.coe P (-1)).mul h
  simpa using this

def intSubB : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := IntAt.mul
  one_mem' := by
    have := IntAt.coe P 1
    simpa using this
  add_mem' := IntAt.add
  zero_mem' := by
    have := IntAt.coe P 0
    simpa using this
  neg_mem' := intAt_negB P

def redHomB : intSubB P →+* (𝓞 E ⧸ P.asIdeal) where
  toFun a := redP P a.1
  map_one' := by
    have := reduction_coe P 1
    simpa using this
  map_mul' a b := reduction_mul a.2 b.2
  map_zero' := by
    have := reduction_coe P 0
    simpa using this
  map_add' a b := reduction_add a.2 b.2

theorem reduction_det_eq_det_reduction₂ {m : ℕ} (A : Matrix (Fin m) (Fin m) E) (hA : ∀ i j, IntAt P (A i j)) :
    redP P A.det = (Matrix.of fun i j => redP P (A i j)).det := by
  let A' : Matrix (Fin m) (Fin m) (intSubB P) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have e1 : A = (intSubB P).subtype.mapMatrix A' := by
    ext i j
    rfl
  have e2 : A.det = ((A'.det : intSubB P) : E) := by
    rw [e1, ← RingHom.map_det]
    rfl
  rw [e2]
  show redHomB P A'.det = _
  rw [RingHom.map_det]
  rfl

theorem reduction_det_congr {m : ℕ} (A B : Matrix (Fin m) (Fin m) E) (hA : ∀ i j, IntAt P (A i j)) (hB : ∀ i j, IntAt P (B i j))
    (h : ∀ i j, redP P (A i j) = redP P (B i j)) : redP P A.det = redP P B.det := by
  rw [reduction_det_eq_det_reduction₂ P A hA, reduction_det_eq_det_reduction₂ P B hB]
  congr 1
  ext i j
  exact h i j

variable {P}

structure MCong (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (M M' : ℕ → ℕ → E) : Prop where
  int : ∀ p p', IntAt P (M' p p') ↔ IntAt P (M p p')
  div : ∀ p p', IntAt P (M' p p' / (q : E)) ↔ IntAt P (M p p' / (q : E))
  red : ∀ p p', redP P (M' p p') = redP P (M p p')

theorem mcong_of {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal) {M Z : ℕ → ℕ → E} (hZ : ∀ p p', IntAt P (Z p p' / (q : E))) :
    MCong P q M (fun p p' => M p p' + Z p p') := by
  have hqE : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq0
  have hqi : IntAt P (q : E) := by
    have := IntAt.coe P (q : 𝓞 E)
    simpa using this
  have hqr : redP P (q : E) = 0 := by
    have := reduction_coe P (q : 𝓞 E)
    rw [map_natCast] at this
    rw [this]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hq
  have hZe : ∀ p p', Z p p' = (q : E) * (Z p p' / (q : E)) := fun p p' => by
    field_simp
  have hZi : ∀ p p', IntAt P (Z p p') := fun p p' => by
    rw [hZe]
    exact hqi.mul (hZ p p')
  have hZr : ∀ p p', redP P (Z p p') = 0 := fun p p' => by
    rw [hZe, reduction_mul hqi (hZ p p'), hqr, zero_mul]
  have hint : ∀ p p', IntAt P (M p p' + Z p p') ↔ IntAt P (M p p') := fun p p' =>
    ⟨fun h => by
      have := h.add (intAt_negB P (hZi p p'))
      simpa using this, fun h => h.add (hZi p p')⟩
  refine ⟨hint, fun p p' => ?_, fun p p' => ?_⟩
  · show IntAt P ((M p p' + Z p p') / (q : E)) ↔ _
    rw [add_div]
    exact ⟨fun h => by
      have := h.add (intAt_negB P (hZ p p'))
      simpa using this, fun h => h.add (hZ p p')⟩
  · show redP P (M p p' + Z p p') = _
    by_cases h : IntAt P (M p p')
    · rw [reduction_add h (hZi p p'), hZr, add_zero]
    · rw [reduction_eq_zero_of_not_integral P h, reduction_eq_zero_of_not_integral P (mt (hint p p').1 h)]

end RedRing

section Loc1

theorem ite_congrB {α : Type} {c c' : Prop} {i : Decidable c} {i' : Decidable c'} {a a' b : α} (h : c ↔ c') (hv : c' → a = a') :
    @ite α c i a b = @ite α c' i' a' b := by
  by_cases hc : c'
  · rw [if_pos hc, if_pos (h.2 hc), hv hc]
  · rw [if_neg hc, if_neg (mt h.1 hc)]

theorem ite_neB {α : Type} {c : Prop} {i : Decidable c} {a b : α} (h : @ite α c i a b ≠ b) : c := by
  by_contra hc
  exact h (if_neg hc)

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem unitV_congrB (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E} (h : redP P a = redP P b) : LocE.unitV χ a = LocE.unitV χ b := by
  unfold LocE.unitV
  rw [h]

theorem fIdx_zeroB (k₀ n s : ℕ) : LocE.fIdx k₀ 0 n s = s := by
  unfold LocE.fIdx
  split_ifs <;> omega

theorem eN_inB (N p : ℕ) (hp : p < N) : Loc.eN E N p = Pi.single (⟨p, hp⟩ : Fin N) (1 : E) := by
  funext l
  unfold Loc.eN
  by_cases h : l.1 = p
  · have hl : l = ⟨p, hp⟩ := Fin.ext h
    rw [if_pos h, hl, Pi.single_eq_same]
  · have hl : l ≠ ⟨p, hp⟩ := fun e => h (congrArg Fin.val e)
    rw [if_neg h, Pi.single_eq_of_ne hl]

theorem eN_outB (N p : ℕ) (hp : ¬ p < N) : Loc.eN E N p = 0 := by
  funext l
  unfold Loc.eN
  rw [if_neg fun h : l.1 = p => hp (h ▸ l.2)]
  rfl

theorem entB_inB (q k₀ n' n : ℕ) (ex' ex : ℕ → ℕ) (x : HomE E (n' + 0) (n + 0)) {p p' : ℕ} (hp : p < n + 0) (hp' : p' < n' + 0) :
    LocE.entB q k₀ 0 n' 0 n ex' ex x p p' = x (Pi.single ⟨p', hp'⟩ 1) ⟨p, hp⟩ := by
  unfold LocE.entB
  rw [fIdx_zeroB, fIdx_zeroB]
  have s1 : LocE.scE n' ex' p' = 0 := by
    unfold LocE.scE
    rw [if_pos (by omega)]
  have s2 : LocE.scE n ex p = 0 := by
    unfold LocE.scE
    rw [if_pos (by omega)]
  rw [s1, s2, sub_zero, zpow_zero, mul_one, eN_inB _ _ hp']
  unfold Loc.atN
  rw [dif_pos hp]

theorem entB_outB (q k₀ n' n : ℕ) (ex' ex : ℕ → ℕ) (x : HomE E (n' + 0) (n + 0)) {p p' : ℕ} (h : ¬ (p < n + 0 ∧ p' < n' + 0)) :
    LocE.entB q k₀ 0 n' 0 n ex' ex x p p' = 0 := by
  unfold LocE.entB
  rw [fIdx_zeroB, fIdx_zeroB]
  by_cases hp : p < n + 0
  · have hp' : ¬ p' < n' + 0 := fun h' => h ⟨hp, h'⟩
    rw [eN_outB _ _ hp', map_zero]
    unfold Loc.atN
    rw [dif_pos hp]
    simp
  · unfold Loc.atN
    rw [dif_neg hp, zero_mul]

theorem entB_addB (q k₀ n' n : ℕ) (ex' ex : ℕ → ℕ) (x z : HomE E (n' + 0) (n + 0)) :
    LocE.entB q k₀ 0 n' 0 n ex' ex (x + z) = fun p p' => LocE.entB q k₀ 0 n' 0 n ex' ex x p p' + LocE.entB q k₀ 0 n' 0 n ex' ex z p p' := by
  funext p p'
  by_cases h : p < n + 0 ∧ p' < n' + 0
  · rw [entB_inB _ _ _ _ _ _ _ h.1 h.2, entB_inB _ _ _ _ _ _ _ h.1 h.2, entB_inB _ _ _ _ _ _ _ h.1 h.2]
    rfl
  · rw [entB_outB _ _ _ _ _ _ _ h, entB_outB _ _ _ _ _ _ _ h, entB_outB _ _ _ _ _ _ _ h, add_zero]

theorem intAt_zeroB : IntAt P (0 : E) := by
  have := IntAt.coe P 0
  simpa using this

theorem entB_mcongB {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal) (k₀ n' n : ℕ) (ex' ex : ℕ → ℕ) (x z : HomE E (n' + 0) (n + 0))
    (hz : ∀ s l, IntAt P ((q : E)⁻¹ * z (Pi.single s 1) l)) :
    MCong P q (LocE.entB q k₀ 0 n' 0 n ex' ex x) (LocE.entB q k₀ 0 n' 0 n ex' ex (x + z)) := by
  rw [entB_addB]
  refine mcong_of hq0 hq fun p p' => ?_
  by_cases h : p < n + 0 ∧ p' < n' + 0
  · rw [entB_inB _ _ _ _ _ _ _ h.1 h.2, div_eq_inv_mul]
    exact hz _ _
  · rw [entB_outB _ _ _ _ _ _ _ h, zero_div]
    exact intAt_zeroB

theorem entB_allIntB (q k₀ n' n a : ℕ) (ha : n' + 0 ≤ a) (ex' ex : ℕ → ℕ) (x : HomE E (n' + 0) (n + 0))
    (h : ∀ p p', p < n + 0 → p' < a → IntAt P (LocE.entB q k₀ 0 n' 0 n ex' ex x p p')) :
    ∀ p p', IntAt P (LocE.entB q k₀ 0 n' 0 n ex' ex x p p') := by
  intro p p'
  by_cases hh : p < n + 0 ∧ p' < n' + 0
  · exact h p p' hh.1 (lt_of_lt_of_le hh.2 ha)
  · rw [entB_outB _ _ _ _ _ _ _ hh]
    exact intAt_zeroB

variable (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

theorem det_congrB {q : ℕ} {M M' : ℕ → ℕ → E} (h : MCong P q M M') (hI : ∀ p p', IntAt P (M p p')) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (m : ℕ) (f g : Fin m → ℕ) :
    LocE.unitV ξ (Matrix.det (Matrix.of fun s s' : Fin m => M' (f s) (g s'))) = LocE.unitV ξ (Matrix.det (Matrix.of fun s s' : Fin m => M (f s) (g s'))) :=
  unitV_congrB ξ (reduction_det_congr P _ _ (fun _ _ => (h.int _ _).2 (hI _ _)) (fun _ _ => hI _ _) fun _ _ => h.red _ _)

theorem phiQ_invB {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' n : ℕ) (hc' : c' = 0)
    (x z : HomE E (n' + c') (n + 0)) (hz : ∀ s l, IntAt P ((q : E)⁻¹ * z (Pi.single s 1) l)) :
    LocE.PhiQ q ξ k₀ r c' n' 0 n (x + z) = LocE.PhiQ q ξ k₀ r c' n' 0 n x := by
  subst hc'
  have h := entB_mcongB hq0 hq k₀ n' n 0 0 x z hz
  unfold LocE.PhiQ
  refine ite_congrB ?_ fun hc => ?_
  · simp only [h.int, h.div]
  · have hI := entB_allIntB q k₀ n' n _ le_rfl _ _ x hc.1
    exact det_congrB h hI ξ _ (fun s => s.1) (fun s => s.1)

theorem phiQ_suppB (q : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' n : ℕ) (hc' : c' = 0)
    (x : HomE E (n' + c') (n + 0)) (hx : LocE.PhiQ q ξ k₀ r c' n' 0 n x ≠ 0) : ∀ s l, IntAt P (x (Pi.single s 1) l) := by
  subst hc'
  unfold LocE.PhiQ at hx
  have hc := ite_neB hx
  intro s l
  have := hc.1 l.1 s.1 l.2 s.2
  rwa [entB_inB _ _ _ _ _ _ _ l.2 s.2] at this

end Loc1

section TopLoc

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem cOf_topB {m2 : ℕ} (hm : R.m = m2 + 2) : cOf R (m2 + 1) = 0 := by
  unfold cOf
  omega

theorem qOf_memB (w : HeightOneSpectrum (𝓞 X.E)) : ((qOf w : ℕ) : 𝓞 X.E) ∈ w.asIdeal := Ideal.absNorm_mem _

end TopLoc

section Gen3

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem map_stdAt3 {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (B : HomE E a b) (hB : ∀ s l, IntAt P (B (Pi.single s 1) l))
    {v : Sp E a} (hv : v ∈ stdAt E a P) : B v ∈ stdAt E b P := by
  refine (ciMem_stdAt P _).2 fun l => ?_
  exact intAt_linear_form_on_std P ((LinearMap.proj l : Sp E b →ₗ[E] E) ∘ₗ B) (fun s => hB s l) hv

end Gen3

section FtY3

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem intAt_qpow3 (w : HeightOneSpectrum (𝓞 X.E)) (k : ℕ) : IntAt w ((qOf w : X.E) ^ k) := by
  rw [← Nat.cast_pow]
  exact intAt_natCast_kernel_local_factors _ _

open Classical in

theorem coupling_index_scaled_mem_local {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Y : Set (Sp X.E n)} (hY : Y ∈ ybSet sel mu cst N)
    (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) :
    Y.Nonempty ∧ ∀ a ∈ Y, ((qOf w.1 : X.E) ^ cst.M) • a ∈ localization₂ w.1.asIdeal N := by
  obtain ⟨y0, hy0, rfl⟩ := hY
  refine ⟨⟨y0, ?_⟩, ?_⟩
  · rw [Set.mem_ofPred_eq, sub_self]
    exact zero_mem _
  · intro a ha
    have h1 := (mem_locLat _ _ _ _).1 hy0 w
    simp only [if_neg hw, zpow_neg, zpow_natCast, inv_inv] at h1
    have h2 := (mem_locLat _ _ _ (a - y0)).1 ha w
    simp only [if_neg hw, zpow_natCast] at h2
    have hq0 : (qOf w.1 : X.E) ^ cst.M ≠ 0 := pow_ne_zero _ (by exact_mod_cast (qOf_pos w.1).ne')
    have e : ((qOf w.1 : X.E) ^ cst.M) • a = ((qOf w.1 : X.E) ^ cst.M) • y0 +
        ((qOf w.1 ^ cst.M * qOf w.1 ^ cst.M : ℕ) : X.E) • (((qOf w.1 : X.E) ^ cst.M)⁻¹ • (a - y0)) := by
      rw [smul_smul]
      push_cast
      rw [mul_assoc, mul_inv_cancel₀ hq0, mul_one, smul_sub]
      abel
    rw [e]
    refine add_mem h1 ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem h2 _

end FtY3

section OrdD

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem intAt_smul_locPD (Q : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)} {c : E} (hc : IntAt Q c) {z : Sp E n}
    (hz : z ∈ localization₂ Q.asIdeal N) : c • z ∈ localization₂ Q.asIdeal N := by
  obtain ⟨r, s, hs, hrs⟩ := hc
  obtain ⟨s', hs', hz'⟩ := (mem_locP Q N z).1 hz
  refine (mem_locP Q N _).2 ⟨s * s', fun h => (Q.isPrime.mem_or_mem h).elim hs hs', ?_⟩
  have e : (s * s') • (c • z) = r • (s' • z) := by
    rw [← algebraMap_smul E (s * s'), ← algebraMap_smul E r, ← algebraMap_smul E s' z, smul_smul, smul_smul, map_mul, ← hrs]
    congr 1
    ring
  rw [e]
  exact N.smul_mem r hz'

theorem exists_frameD (Q : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) :
    ∃ f : Sp E n ≃ₗ[E] Sp E n, IsFrAt Q N f := by
  obtain ⟨β, hβ, hint⟩ := exists_locBasis Q hN
  refine ⟨β.equivFun.symm, fun y => ⟨fun h => (ciMem_stdAt Q y).2 fun i => ?_, fun h => ?_⟩⟩
  · have h2 := hint _ h i
    have e := congrFun (β.equivFun.apply_symm_apply y) i
    rw [Module.Basis.equivFun_apply] at e
    rwa [e] at h2
  · rw [Module.Basis.equivFun_symm_apply]
    exact Submodule.sum_mem _ fun i _ => intAt_smul_locPD Q ((ciMem_stdAt Q y).1 h i) (hβ i)

end OrdD

end Formalism.L2.Ker
