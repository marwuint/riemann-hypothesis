module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NonnegSubOfLt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardStabilizerForgetFr
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa

@[expose] public section

noncomputable section

namespace GlobalTheory.TilClass

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
open GlobalTheory.TopStep (sumE prH extI redGL)

section Points

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} (hN : N = n + 1)
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

variable (hconj : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
  (hbig : 2 ^ Module.finrank ℚ E < ∏ P ∈ ST, Ideal.absNorm P.asIdeal) {pi : 𝓞 E}
  (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
include hconj hbig hT hG

end Points

section Size

variable {X : Fields} {Pr : Primes X}

end Size

section Branch

theorem isBlock_of_mulVec {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) {A' : Matrix (Fin N) (Fin N) E}
    {A : Matrix (Fin n) (Fin n) E} (h1 : ∀ x, iniH hN (A'.mulVec x) = A.mulVec (iniH hN x))
    (h2 : ∀ x, A'.mulVec x (Br.iL hN) = x (Br.iL hN)) : BranchFormula.IsBlock hN A' A 1 := by
  have hne : ∀ a : Fin n, Br.iC hN a ≠ Br.iL hN := fun a h => absurd (congrArg Fin.val h) a.2.ne
  have hinj : Function.Injective (Br.iC hN) := fun a b h => Fin.ext (congrArg Fin.val h :)
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have h := congrFun (h1 (Pi.single (Br.iC hN b) 1)) a
    have e : iniH hN (Pi.single (Br.iC hN b) (1 : E)) = Pi.single b 1 := funext fun i => by
      simp only [iniH, Pi.single_apply, hinj.eq_iff]
    rwa [e, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  · have h := congrFun (h1 (Pi.single (Br.iL hN) 1)) a
    have e : iniH hN (Pi.single (Br.iL hN) (1 : E)) = 0 := funext fun i => Pi.single_eq_of_ne (hne i) _
    rwa [e, Matrix.mulVec_single_one, Matrix.mulVec_zero] at h
  · have h := h2 (Pi.single (Br.iC hN a) 1)
    rwa [Matrix.mulVec_single_one, Pi.single_eq_of_ne (hne a).symm] at h
  · have h := h2 (Pi.single (Br.iL hN) 1)
    rwa [Matrix.mulVec_single_one, Pi.single_eq_same] at h

theorem brStd_rhoVr {E K ι : Type} [Field E] [Field K] [CharZero K] [Fintype ι] {N n : ℕ} (hN : N = n + 1) (e : ι → E →+* K)
    {lam : ι → DomWeight N} {sg : ι → DomWeight n} (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ))
    (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) {γ' : GL (Fin N) E} {γ : GL (Fin n) E}
    (h : BranchFormula.IsBlock hN ((γ'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
      ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) 1) (G : VV K lam) :
    Br.brStd hN lam sg (rhoVr e lam γ' G) = rhoVr e sg γ (Br.brStd hN lam sg G) := by
  refine BranchFormula.equivariance K ι N n hN lam sg hI hS (invTrK (embGL e γ)) (invTrK (embGL e γ')) (fun τ => ?_) G
  have e1 : ∀ {m : ℕ} (g : GL (Fin m) E) (a b : Fin m), ((invTrK (embGL e g) τ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) a b =
      e τ (((g⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) b a) := fun g a b => rfl
  simp only [e1]
  refine ⟨fun a b => by rw [h.1], fun a => ⟨by rw [(h.2.1 a).2, map_zero], by rw [(h.2.1 a).1, map_zero]⟩, by rw [h.2.2, map_one]⟩

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (lam : ι → DomWeight n)

theorem mem_ValC_iff (f : Fr emb σ n → ℂ) :
    f ∈ ValC (Gr emb σ n) lam ↔ ∃ F : VV ℂ lam, fnOf (Gr emb σ n) (shiftOf lam) 1 F.1 = f := by
  have e : ∀ F : VV ℂ lam, evV (embAt σ emb) (1 : Matrix (Fin n) (Fin n) E) lam (RingHom.id ℂ) F =
      fnOf (Gr emb σ n) (shiftOf lam) 1 F.1 := fun F => by
    rw [evV_apply, MvPolynomial.map_id]
    rfl
  constructor
  · intro hf
    have h : f ∈ Submodule.span ℂ (Set.range (evV (embAt σ emb) (1 : Matrix (Fin n) (Fin n) E) lam (RingHom.id ℂ))) := by
      rwa [span_evV]
    rw [← LinearMap.coe_range, Submodule.span_eq] at h
    obtain ⟨F, rfl⟩ := h
    exact ⟨F, (e F).symm⟩
  · rintro ⟨F, rfl⟩
    rw [← e]
    exact evV_mem_ValC _ _ _ _ F

theorem trFr_fnOf (γ : GL (Fin n) E) (c : Kˣ) (F : VV ℂ lam) :
    trFr emb σ γ c (fnOf (Gr emb σ n) (shiftOf lam) 1 F.1) =
      σ c • fnOf (Gr emb σ n) (shiftOf lam) 1 (rhoVr (embAt σ emb) lam γ F).1 := by
  funext y
  rw [trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  have h := evV_rhoVr_tr (embAt σ emb) (1 : Matrix (Fin n) (Fin n) E) lam (RingHom.id ℂ) γ F y (frMul emb σ γ⁻¹ y) fun τ =>
    (congrFun (congrArg Subtype.val ((frEquiv emb σ γ).apply_symm_apply y)) τ).symm
  rw [evV_apply, evV_apply, MvPolynomial.map_id, MvPolynomial.map_id] at h
  exact h.symm

theorem polOf_fnOf_one (sh : ι → ℤ) (F : Pol ℂ ι n) :
    polOf (Gr emb σ n) sh (fr0 emb σ n) (fnOf (Gr emb σ n) sh 1 F) = F := by
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  have h := polOf_fnOf (Gr emb σ n) sh (fr0 emb σ n) F
  rwa [e] at h

end Branch

section Period

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (Q : PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R)

variable {Q}

end Period

section Levels

variable {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) {N n : ℕ} (hN : N = n + 1)
  {Q : Finset (HeightOneSpectrum (𝓞 X.E))} (hQ : ∀ P : Q, Pr.piT u ∉ P.1.asIdeal)
  {Λ : LevFam X.E X.K N Pr.vGs} {Θ : LevQFam X.E X.K N Q} {Λ' : LevFam X.E X.K n Pr.vGs} {Θ' : LevQFam X.E X.K n Q}
include hX hPr hQ

variable (hΛ : ∀ h, extGH hN h ∈ Λ.grp ↔ h ∈ Λ'.grp) (hΘ : ∀ c, extQ X.E hN Q c ∈ Θ.grp ↔ c ∈ Θ'.grp)
include hΛ hΘ

end Levels

section Lattices

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (P : LevFam X.E X.K R.r Pr.vGs)

variable (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word)
  (rho : ∀ i (b : Idx sel mu L i), (stepAt sel mu cst L Tp u i).D b → ℂ)
  (rho' : ∀ i (b : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u (i + 1)).D b → ℂ) (cD : X.Tau → ℂ)
  (Th : ∀ i (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u i).D b →
    (stepAt sel mu cst L Tp u (i + 1)).D b' → Formalism.L2.Ker.VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ)

variable {W Ch sel mu cst L P Tp u rho rho' cD Th} {Q : PerIn (chainAt sel mu cst L Tp u rho rho' cD Th)}

end Lattices

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (P : LevFam X.E X.K R.r Pr.vGs)

end Main

section Top

open GlobalTheory.TopStep (TilOk tilTop tilEl topLevG topLevQ topGSD evTop TopDepth inQ)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word}

theorem brC_rho (hW : W.Ok) (γ : UF X.E (R.N R.m - 1)) (x : VV X.K (W.lamTrue u R.m)) :
    brC W u (rhoVr X.emb (W.lamTrue u R.m) (ufGL X.E _ (extUH (N_m_succ R) γ)) x) =
      rhoVr X.emb W.sgTrue (ufGL X.E _ γ) (brC W u x) := by
  have h := brStd_rhoVr (N_m_succ R) X.emb (fun τ => (BranchMembers.members X _ R W hW u τ).1)
    (fun τ => (BranchMembers.members X _ R W hW u τ).2) (γ' := ufGL X.E _ (extUH (N_m_succ R) γ)) (γ := ufGL X.E _ γ) (by
      have e : ∀ y, ((ufGL X.E _ (extUH (N_m_succ R) γ⁻¹) : GL _ _) : Matrix _ _ X.E).mulVec y =
          sumE (N_m_succ R) (γ⁻¹).1 1 y := fun y => by
        rw [← TopStep.extUH_val]
        exact toGLm_mulVec _ y
      rw [← map_inv, ← map_inv, ← map_inv]
      refine isBlock_of_mulVec _ (fun y => ?_) fun y => ?_
      · rw [e]
        exact (TopStep.prH_sumE _ _ _ y).trans (toGLm_mulVec _ _).symm
      · rw [e, TopStep.sumE_last, Units.val_one, one_mul]) x
  rw [brC, Br.brAt, LinearMap.smul_apply, LinearMap.smul_apply, h, map_smul]

end Top

end GlobalTheory.TilClass
