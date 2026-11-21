import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Eps0UnramFrob
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicEmbeddingsConjugate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingIntegralContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmallIdealNeBot

noncomputable section

namespace GlobalTheory.EigTie

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Formalism.MainNotions.IntegralHeckeForms (HkIdx V0 Fm0 eG Eigsp)
open Formalism.MainNotions.BlochKatoReduction.Gen (goodE Tmat eps0 chiS)
open Formalism.L2.Host (HChar CharFrame embLL0)
open GlobalTheory.Triple (Reading embSide muBase heckeVal IsParam IsResidual FbAt jIdx)
open GlobalTheory.TripleGal (HkFrob)
open GlobalTheory.HeightCounting (RowSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
open scoped TensorProduct

variable {D : D7}

section Sys

variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

def IsEigVec (i : X.Tw) (j : ℕ) (b : Bool) (ev : ℕ → PlE D.host → FractionRing (X.O i)) (x : Y.Fm i j b) : Prop :=
  x ∈ V0 Y i j b ∧ x ≠ 0 ∧ ∀ k P, HkIdx i k P → Y.hkF i j b k P x = ev k P • x

def IsEigSys (i : X.Tw) (j : ℕ) (b : Bool) (ev : ℕ → PlE D.host → FractionRing (X.O i)) : Prop :=
  ∃ x, IsEigVec Y i j b ev x

def sigEv {i : X.Tw} (s : X.Sig i) (k : ℕ) (P : PlE D.host) : FractionRing (X.O i) :=
  algebraMap (X.O i) (FractionRing (X.O i)) (X.hEig i s k P)

variable {Y} {i : X.Tw} {j : ℕ} {b : Bool}

end Sys

section Read

variable (X : NTw D.R D.host D.what₂ D.LL0 D.nd)

def fracMap (i : X.Tw) : FractionRing (X.O0 i) →+* FractionRing (X.O i) :=
  IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i)) (L := FractionRing (X.O i)) (X.O_inj i)

def embO (i : X.Tw) (b : Bool) : ↥D.LL0 →+* FractionRing (X.O i) := (fracMap X i).comp (embSide X i b)

theorem fracMap_algebraMap (i : X.Tw) (x : X.O0 i) :
    fracMap X i (algebraMap (X.O0 i) (FractionRing (X.O0 i)) x) =
      algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i) x) :=
  by simp [fracMap, IsFractionRing.map]

structure CoefRead (i : X.Tw) (b : Bool) where

  F : Type
  [fld : Field F]

  e : ↥D.LL0 →+* F

  u : F →+* FractionRing (X.O i)

  toC : F →+* ℂ
  u_e : ∀ x, u (e x) = embO X i b x
  toC_e : ∀ x, toC (e x) = embLL0 D x

attribute [instance] CoefRead.fld

variable {X} {i : X.Tw} {b : Bool}

end Read

section Par

def IsRowPar (Rw : RowSide D) (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop :=
  IsParam σ π ∧ ∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR σ w

def liftIdx {j : ℕ} (hj : j ∈ Finset.Icc 1 D.R.m) : Fin D.R.m := ⟨j - 1, by have := Finset.mem_Icc.1 hj; omega⟩

variable (C : CharFrame D) (Rw : RowSide D) {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X)

variable {C Rw Y} {i : X.Tw} {b : Bool}

theorem liftIdx_jS (s : X.Sig i) : liftIdx (Finset.mem_Icc.2 (X.jS_range i s)) = jIdx s := rfl

end Par

section Res

variable (Rw : RowSide D)

def IsoInduces {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) : Prop :=
  ∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val w x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1

def TeichAt {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) (red : Zbar l →+* FbAt D w) : Prop :=
  ∀ k, l ≠ D.host.g k → ∀ (v : D.nd.PlG k) x, x ≠ 0 → ∀ z : Zbar l,
    (z : Qbar l) = ι.symm (D.ntypes.teichC k x) → red z = D.ntypes.iota k v w x

def ResAt {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) (red : Zbar l →+* FbAt D w) : Prop :=
  IsoInduces ι w ∧ TeichAt ι w red ∧
    ∀ σ π (r : GalE D →* GL (Fin D.R.r) (Qbar l)), D.nd.goodRow σ → OnW D σ → IsRowPar Rw σ π →
      IsGaloisRepOf D π l ι r → IsResidual ι r σ w red

end Res

def ResTied (D : D7) (Rw : RowSide D) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ (l : ℕ) [Fact l.Prime], D.what₂.places.resChar w = l →
    ∃ (ι : Qbar l ≃+* ℂ) (red : Zbar l →+* FbAt D w), ResAt Rw ι w red

section Bridge

theorem ball_of_int {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] (a b : L →+* Qbar l)
    (h : ∀ x : 𝓞 L, ‖a x‖ < 1 ↔ ‖b x‖ < 1) (x : L) : ‖a x‖ ≤ 1 ↔ ‖b x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff
  | exact _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff
  | (apply _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff ..)

theorem val_pos_iff (w : D.what₂.places.Pl) {x : D.what₂.LL} (hx : x ≠ 0) :
    0 < D.what₂.places.val w x ↔ ¬ 0 ≤ D.what₂.places.val w x⁻¹ := by
  have h := (D.what₂.places.val w).map_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, AddValuation.map_one, D.val_eq w x hx, D.val_eq w _ (inv_ne_zero hx)] at h
  rw [D.val_eq w x hx, D.val_eq w _ (inv_ne_zero hx)]
  norm_cast at h ⊢
  omega

theorem IsoInduces.lt_iff {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {w : D.what₂.places.Pl} (h : IsoInduces ι w)
    (x : D.what₂.LL) : 0 < D.what₂.places.val w x ↔ ‖ι.symm (D.what₂.embLL x)‖ < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖ι.symm (D.what₂.embLL x)‖ := by simpa using hx
    rw [val_pos_iff w hx, h, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ h0, not_le]

theorem resChar_eq {w : D.what₂.places.Pl} {l : ℕ} (hl : l.Prime) (h : 0 < D.what₂.places.val w (l : D.what₂.LL)) :
    D.what₂.places.resChar w = l := by
  by_contra hne
  have hp := D.what₂.places.resChar_prime w
  have h1 : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [D.what₂.places.val_resChar]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hint : ∀ n : ℤ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := fun n => by
    have hn : ∀ n : ℕ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := fun n => by
      induction n with
      | zero => simp
      | succ n ih => rw [Nat.cast_succ]; exact (D.what₂.places.val w).map_le_add ih (by simp)
    obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
    · simpa using hn n
    · rw [Int.cast_neg, AddValuation.map_neg]; simpa using hn n
  obtain ⟨a, b, e⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hne)
  have e' : (a : D.what₂.LL) * (D.what₂.places.resChar w : ℕ) + (b : D.what₂.LL) * l = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → D.what₂.LL) e
  have := (D.what₂.places.val w).map_lt_add (g := 0) (x := (a : D.what₂.LL) * (D.what₂.places.resChar w : ℕ))
    (y := (b : D.what₂.LL) * l) (by rw [AddValuation.map_mul]; exact h1.trans_le (le_add_of_nonneg_left (hint a)))
    (by rw [AddValuation.map_mul]; exact h.trans_le (le_add_of_nonneg_left (hint b)))
  rw [e', AddValuation.map_one] at this
  exact lt_irrefl _ this

variable {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool}

theorem norm_lt_iff (ρ : Reading X i b) (z : FractionRing (X.O0 i)) :
    (∃ y ∈ IsLocalRing.maximalIdeal (X.O0 i), algebraMap (X.O0 i) (FractionRing (X.O0 i)) y = z) ↔ ‖ρ.κ z‖ < 1 := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.padicAlgCl_embedding_bounded_continuous (X.l i) (X.twistBaseCoefficientRing_isAdic i) (GlobalTheory.GalChar.toQ ρ.κ) ρ.κ_alg
  refine ⟨fun ⟨y, hy, e⟩ => e ▸ h2 y hy, fun h => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, zero_mem _, map_zero _⟩
  have h0 : 0 < ‖ρ.κ z‖ := by simpa using hz
  rcases ValuationRing.isInteger_or_isInteger (X.O0 i) z with ⟨y, e⟩ | ⟨y, e⟩
  · refine ⟨y, ?_, e⟩
    by_contra hy
    obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.1 hy
    have e1 : ‖GlobalTheory.GalChar.toQ ρ.κ u‖ * ‖GlobalTheory.GalChar.toQ ρ.κ (u⁻¹ : (X.O0 i)ˣ)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    have e2 : ‖GlobalTheory.GalChar.toQ ρ.κ u‖ < 1 := by rw [← e] at h; exact h
    exact (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) e2 (h1 _)).ne e1
  · have := h1 y
    change ‖ρ.κ (algebraMap _ _ y)‖ ≤ 1 at this
    rw [e, map_inv₀, norm_inv, inv_le_one₀ h0] at this
    exact absurd h (not_lt.2 this)

theorem exists_reading_of_induces {b' : Bool} (ρ : Reading X i b') {ι : Qbar (X.l i) ≃+* ℂ} {w : D.what₂.places.Pl}
    (h : IsoInduces ι w) (hw : ∀ x : ↥D.LL0, 0 ≤ D.what₂.places.val w x ↔ ‖ρ.κ (embSide X i b x)‖ ≤ 1) :
    ∃ ρ' : Reading X i b, ρ'.ι = ι := by
  obtain ⟨g, hg⟩ := GlobalTheory.EmbUnitBallConj.exists_conj (X.l i) ↥D.LL0 (ρ.κ.comp (embSide X i b))
    (ι.symm.toRingHom.comp (embLL0 D)) fun x => (hw x).symm.trans (h x)
  refine ⟨⟨(g : Qbar (X.l i) →+* Qbar (X.l i)).comp ρ.κ, ι, fun z => ?_, fun x => ?_⟩, rfl⟩
  · rw [RingHom.comp_apply, ρ.κ_alg]
    exact g.commutes _
  · exact (congrArg ι (hg x)).trans (ι.apply_symm_apply _)

end Bridge

namespace Model

open Formalism.MainNotions.BlochKatoReduction (scalGL)

variable (D)

def val (i : D.ntw.Tw) (k : ℕ) (P : PlE D.host) : D.ntw.O0 i :=
  (D.R.r.choose k : D.ntw.O0 i) * Ring.inverse ((normV P : ℕ) : D.ntw.O0 i) ^ (D.R.t * k + k * (k - 1) / 2)

@[reducible] def tw : @NTw D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd :=
  { D.ntw with
    Sig := fun _ => Fin D.R.m × Bool
    finSig := fun _ => inferInstance
    jS := fun _ s => s.1.1 + 1
    jS_range := fun _ s => ⟨Nat.le_add_left _ _, s.1.2⟩
    side := fun _ s => s.2
    rhoS := fun i s => (scalGL D.R.r).comp (D.ntw.chi1 i (s.1.1 + 1) s.2)
    rhoS_cont := fun i s => (continuous_pi fun _ => D.ntw.twistCharacterFamily_continuous i (s.1.1 + 1) s.2).matrix_diagonal
    hEig := fun i _ k P => algebraMap (D.ntw.O0 i) (D.ntw.O i) (val D i k P)
    B := fun i _ _ => D.ntw.O i
    acgB := fun _ _ _ => inferInstance
    modB := fun _ _ _ => inferInstance
    freeB := fun _ _ _ => inferInstance
    finB := fun _ _ _ => inferInstance
    Theta := fun _ _ _ => ⊤
    ThetaPsi := fun _ _ _ _ _ _ => ⊤
    ThetaPsi_one := fun _ _ _ _ => (Submodule.baseChange_top _).symm
    hk := fun i _ _ k P => algebraMap (D.ntw.O0 i) (D.ntw.O i) (val D i k P) • 1
    hk_zero := fun i _ _ P => by simp [val] }

open Classical in

@[reducible] def ex : @NExp D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd (tw D) :=
  { D.nexp with
    Fm := fun i _ _ => FractionRing (D.ntw.O i)
    acgFm := fun _ _ _ => inferInstance
    modFmK := fun _ _ _ => inferInstance
    modFmO := fun _ _ _ => inferInstance
    towFm := fun _ _ _ => inferInstance
    fdFm := fun _ _ _ => inferInstance
    actG := fun _ _ _ => 1
    U := ⊥
    psiU := fun _ _ => 1
    eAlg := fun _ _ => 1
    eLL0 := fun g => if 1 = g then 1 else 0
    eAlg_def := fun i b g => by
      by_cases h : 1 = g
      · subst h
        simp [MonoidAlgebra.one_def]
      · simp [MonoidAlgebra.one_def, h]
    eAlg_idem := fun _ _ => mul_one _
    eAlg_central := fun _ _ x => by rw [one_mul, mul_one]
    Bsup := fun i _ _ => LinearMap.range (Algebra.linearMap (D.ntw.O i) (FractionRing (D.ntw.O i)))
    Dat := fun _ _ _ => Empty
    th := fun _ _ _ a => a.elim
    lev := fun _ _ _ a => a.elim
    thPsi := fun _ _ _ _ _ _ a => a.elim
    thPsi_one := fun _ _ _ _ a => a.elim
    thU := fun _ _ _ _ _ a => a.elim
    twPsi := fun i _ _ k _ => TensorProduct.mk (D.ntw.O i) (D.ntw.Ok i k) (FractionRing (D.ntw.O i)) 1
    twPsi_one := fun _ _ _ _ _ => rfl
    twDel := fun _ _ _ _ _ => 0
    thP := fun _ _ _ _ _ _ => 0
    hkF := fun i _ _ k P => algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
      (algebraMap (D.ntw.O0 i) (D.ntw.O i) (val D i k P)) • LinearMap.id
    embB := fun i _ _ => Algebra.linearMap (D.ntw.O i) (FractionRing (D.ntw.O i))
    embB_inj := fun i _ _ => IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))
    eH := fun _ _ _ => 1
    eH_idem := fun _ _ _ => mul_one _ }

variable {D}

end Model

end GlobalTheory.EigTie

end
