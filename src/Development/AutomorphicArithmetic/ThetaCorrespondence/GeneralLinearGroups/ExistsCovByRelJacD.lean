import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FPiece
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section SlopeTestRemainingChoices

open GlobalTheory.JacStages GlobalTheory.JacStagesExact GlobalTheory.ParIndExact GlobalTheory.CompanionTheory.Hypotheses₂.TD GlobalTheory.SplitRead

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_covBy_relJacD {s : ℕ} {d t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V]
    [Module ℂ V] {Θ : Representation ℂ (∀ a, Levi k fun b => Fin (d' a b)) U} (hΘ : Θ.IsIrreducible)
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ)
    (h : IsSubquotient Θ (relJacD e' ρ)) :
    ∃ S T : Subrepresentation ρ, T ⋖ S ∧ IsSubquotient Θ (relJacD e' (subQuot S T)) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded ρ).1 hl
  refine exists_covBy_of_split (fun (S T : Subrepresentation ρ) => IsSubquotient Θ (relJacD e' (subQuot S T)))
    ?_ ?_ ⊤ ⊥ bot_le ?_
  · rintro S ⟨R, f, hf⟩
    haveI := subsingleton_subQuot_self S
    haveI := Model.nontrivial_of_isIrreducible hΘ
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    obtain ⟨⟨v, hv⟩, rfl⟩ := hf u
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain rfl : z = 0 := Subsingleton.elim _ _
    exact hu (map_zero f)
  · intro S M T hTM hMS hQ
    obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := ρ) hTM hMS
    refine isSubquotient_dichotomy (relJacMap e' ι) (relJacMap e' p) hΘ (fun x hx => ?_) hQ
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : p v ∈ twKer (subQuot S M) (relUnipD k e') 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨v', hv', h2⟩ := GlobalTheory.SmGL.Exponents.Additive.exists_mem_twKer p hp _ h1
    obtain ⟨u, hu⟩ := hex (v - v') (by rw [map_sub, h2, sub_self])
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v
    rw [hu]
    exact (Submodule.Quotient.eq _).2 (by simpa using hv')
  · obtain ⟨ι, hι⟩ := subQuot_top_bot ρ
    exact h.trans (isSubquotient_relJacD k s d t d' e' _ _ _ _ ((isSubquotient_subQuot _ _).isSmooth hρ)
      (.of_injective ι hι))

private theorem coarse (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {s : ℕ} (t : Fin s → ℕ) (x : ∀ a, Fin (t a) → IrrGL k) (w : IrrGL k)
    (hx : ∑ c : Fin (∑ a, t a), (x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).1 = w.1)
    (h : jm (fun c : Fin (∑ a, t a) => x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) hx w.rep ≠ 0) :
    ∃ (σ : Fin s → IrrGL k) (hσ : ∑ a, (σ a).1 = w.1), jm σ hσ w.rep ≠ 0 ∧
      ∀ a, ∃ ha : ∑ b, (x a b).1 = (σ a).1, jm (x a) ha (σ a).rep ≠ 0 := by
  classical
  let d : Fin s → ℕ := fun a => ∑ b, (x a b).1
  have hd : ∑ a, d a = w.1 := by
    rw [← hx, Equiv.sum_comp finSigmaFinEquiv.symm (fun p : (Σ a, Fin (t a)) => (x p.1 p.2).1), Fintype.sum_sigma]
  let e := stdBlocks d hd
  let e' : ∀ a, (Σ b, Fin ((x a b).1)) ≃ Fin (d a) := fun a => stdBlocks (fun i => (x a i).1) rfl
  obtain ⟨φR⟩ := _root_.GlobalTheory.JacStages.piTensor_flatHom_equiv s t (fun a b => GL (Fin ((x a b).1)) k) _ fun a b => (x a b).rep
  obtain ⟨φS⟩ := _root_.GlobalTheory.JacStagesProof.jac_refinePlace_equiv k s w.1 d e t (fun a b => (x a b).1) e' _ w.rep
  obtain ⟨φP⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (stdBlocks _ hx) (refinePlace e e') _).2 w.rep
  have hirr0 : (piTensor fun c : Fin (∑ a, t a) =>
      (x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).rep).IsIrreducible :=
    _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun c => (x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).2.rep
  have hirr1 := GlobalTheory.FinGL.Transport.isIrreducible_comp _
    (flatHom fun a b => GL (Fin ((x a b).1)) k) (flatHom_surjective _) hirr0
  have hirr : (piTensor fun a => piTensor fun b => (x a b).rep).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv φR hirr1
  have h1 := (jhMult_ne_zero_iff.1 h).trans (isSubquotient_of_equiv φP)
  have h2 : IsSubquotient (piTensor fun a => piTensor fun b => (x a b).rep) (relJacD e' (jac e w.rep)) :=
    (isSubquotient_of_equiv φR.symm).trans ((SupportUnique.isSubquotient_comp h1
      (flatHom fun a b => GL (Fin ((x a b).1)) k)).trans (isSubquotient_of_equiv φS))
  have hsm := isSmooth_jac e w.2.rep.smooth
  obtain ⟨S, T, hST, h3⟩ := exists_covBy_relJacD e' hirr hsm
    ((hBZ k).2.1 _ _ _ e _ w.rep w.2.rep.smooth (hasFiniteLength_of_isIrreducible w.2.rep.irr)) h2
  have hτ := isIrreducible_subQuot hST
  obtain ⟨σ, hσ⟩ := GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac hG k w.1 (Irr.ofIrrRep w.2.rep) s d e _
    (subQuot S T) hτ (isSubquotient_subQuot S T)
  let σ' : Fin s → IrrGL k := fun a => IrrGL.of (σ a).π (σ a).smooth (σ a).irr
  have hσi : (piTensor fun a => (σ' a).rep).IsIrreducible := _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun a => (σ' a).2.rep
  have hσs : IsSmooth (piTensor fun a => (σ' a).rep) := isSmooth_piTensor fun a => (σ' a).2.rep.smooth
  have h4 : IsSubquotient (subQuot S T) (piTensor fun a => (σ' a).rep) :=
    hσ.trans (GlobalTheory.piTensor_isSubquotient_of_forall _ _ _ _ _ _ fun a =>
      isSubquotient_of_equiv (IrrGL.equivOf (σ a).π (σ a).smooth (σ a).irr))
  obtain ⟨ψ⟩ := SupportUnique.nonempty_equiv_of_isSubquotient hτ hσi h4
  refine ⟨σ', hd, jhMult_ne_zero_iff.2 ((isSubquotient_of_equiv ψ).trans (isSubquotient_subQuot S T)),
    fun a => ⟨rfl, jhMult_ne_zero_iff.2 ?_⟩⟩
  obtain ⟨φT⟩ := _root_.GlobalTheory.JacStages.relJacD_piTensor_equiv k s d t (fun a b => (x a b).1) e' _ fun a => (σ' a).rep
  have h5 := h3.trans ((isSubquotient_relJacD k s d t _ e' _ _ _ _ hσs h4).trans (isSubquotient_of_equiv φT))
  have hi : ∀ a, (piTensor fun b => (x a b).rep).IsIrreducible := fun a =>
    _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun b => (x a b).2.rep
  exact SupportUnique.isSubquotient_factor (fun a => jac (e' a) (σ' a).rep) a (hi a)
    ((isSubquotient_comp_mulSingle (fun a => piTensor fun b => (x a b).rep) hi a).trans
      (SupportUnique.isSubquotient_comp h5 _))

private theorem supp_jm (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {s : ℕ} {y : Fin s → IrrGL k} {w : IrrGL k} {hy : ∑ a, (y a).1 = w.1} (h : jm y hy w.rep ≠ 0)
    {A : Multiset (IrrGL k)} (hA : HasSupport w.rep A) {T : Fin s → Multiset (IrrGL k)}
    (hT : ∀ a, HasSupport (y a).rep (T a)) : A = ∑ a, T a := by
  obtain ⟨u, hu, rfl⟩ := exists_sum_of_jac hG hBZ hA (stdBlocks (fun a => (y a).1) hy)
    (_root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun a => (y a).2.rep) (jhMult_ne_zero_iff.1 h) (fun a => (y a).2.rep)
    (fun a => isSubquotient_comp_mulSingle (fun a => (y a).rep) (fun a => (y a).2.rep.irr) a)
  exact Finset.sum_congr rfl fun a _ => hasSupport_unique hG hBZ (hu a) (hT a)

private theorem jm_cast {L L' : ℕ} (hL : L = L') (y : Fin L' → IrrGL k) (z : Fin L → IrrGL k)
    (hz : ∀ c, z c = y (Fin.cast hL c)) (w : IrrGL k) (hy : ∑ a, (y a).1 = w.1) (h : jm y hy w.rep ≠ 0) :
    ∃ hz : ∑ a, (z a).1 = w.1, jm z hz w.rep ≠ 0 := by
  subst hL
  obtain rfl : z = y := funext hz
  exact ⟨hy, h⟩

private theorem merge (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {s L : ℕ} (t : Fin s → ℕ) (hL : ∑ a, t a = L) {y : Fin L → IrrGL k} {w : IrrGL k} {hy : ∑ a, (y a).1 = w.1}
    (h : jm y hy w.rep ≠ 0) {T : Fin L → Multiset (IrrGL k)} (hT : ∀ a, HasSupport (y a).rep (T a)) :
    ∃ (σ : Fin s → IrrGL k) (hσ : ∑ a, (σ a).1 = w.1), jm σ hσ w.rep ≠ 0 ∧
      ∀ a, HasSupport (σ a).rep (∑ b, T (Fin.cast hL (finSigmaFinEquiv ⟨a, b⟩))) := by
  let x : ∀ a, Fin (t a) → IrrGL k := fun a b => y (Fin.cast hL (finSigmaFinEquiv ⟨a, b⟩))
  obtain ⟨hx, h1⟩ := jm_cast hL y (fun c => x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)
    (fun c => by simp [x]) w hy h
  obtain ⟨σ, hσ, h2, h3⟩ := coarse hG hBZ t x w hx h1
  refine ⟨σ, hσ, h2, fun a => ?_⟩
  obtain ⟨ha, h4⟩ := h3 a
  obtain ⟨A, hA⟩ := exists_hasSupport hBZ hG (σ a)
  rw [← supp_jm hG hBZ h4 hA fun b => hT _]
  exact hA

private theorem deg_eq_zero {y : IrrGL k} {A : Multiset (IrrGL k)} (hA : HasSupport y.rep A) (h0 : A = 0) :
    y.1 = 0 := by
  have h := hA.sum_fst
  rw [h0] at h
  simpa using h.symm

private theorem multiProd_placing {h N : ℕ} {d : Fin h → ℕ} (e e' : (Σ i, Fin (d i)) ≃ Fin N)
    (s : ∀ i, IrrRep (GL (Fin (d i)) k)) :
    IsSubquotient (multiProd e fun i => (s i).ρ) (multiProd e' fun i => (s i).ρ) := by
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e e' _).1 (piTensor fun i => (s i).ρ)
  exact isSubquotient_of_equiv φ

end SlopeTestRemainingChoices

