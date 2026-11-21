import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexForms
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

noncomputable section

namespace GlobalTheory.TilClass

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
open GlobalTheory.TopStep (sumE prH extI redGL)

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
    rw [e, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    exact h
  · have h := congrFun (h1 (Pi.single (Br.iL hN) 1)) a
    have e : iniH hN (Pi.single (Br.iL hN) (1 : E)) = 0 := funext fun i => Pi.single_eq_of_ne (hne i) _
    rw [e, Matrix.mulVec_single_one, Matrix.mulVec_zero] at h
    exact h
  · have h := h2 (Pi.single (Br.iC hN a) 1)
    rw [Matrix.mulVec_single_one, Pi.single_eq_of_ne (hne a).symm] at h
    exact h
  · have h := h2 (Pi.single (Br.iL hN) 1)
    rw [Matrix.mulVec_single_one, Pi.single_eq_same] at h
    exact h

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
      rw [span_evV]
      exact hf
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
