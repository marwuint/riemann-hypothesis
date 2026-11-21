import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAtSeesawProductDatumEqVacuumCombinations
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumOfCarriesLatticeCompletions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCoreStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocPlOff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsFoldr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCombAtReN
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentTopStandardCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawCombinationsCompositeNeZeroOfVacuumStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.DatumTopAt

section Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem combAt_mono' {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ x, P x → Q x) {c : WO S T →₀ ℂ}
    (hc : GlobalTheory.FinPl.CombAt P c) : GlobalTheory.FinPl.CombAt Q c := fun x hx => GlobalTheory.DisjComb.mxAt_mono h (hc x hx)

theorem vac_mono' {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} (P : GlobalTheory.FinPl.Pl D → Prop) {f : WO S T → ℂ}
    (h : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) f) : GlobalTheory.FinPl.Vac ψ S T LS LT P f := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True :=
    AddSubgroup.closure_mono fun w ⟨α, hα, _, hw⟩ => ⟨α, hα, fun _ h => absurd trivial h, hw⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem locPl_combAt {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (Lp : LocPl ψ S T M M') :
    GlobalTheory.FinPl.CombAt (· = Lp.q.v) Lp.o ∧ GlobalTheory.FinPl.CombAt (· = Lp.q.v) Lp.e :=
  ⟨fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D Lp.k Lp.q u (Lp.o_at u hu),
    fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D Lp.k Lp.q u (Lp.e_is.1 u hu)⟩

theorem comm_list (hψ : IsStdChar D ψ (-1)) {n : ℕ} (pv : Fin n → GlobalTheory.FinPl.Pl D) (hv : Function.Injective pv)
    (a b : Fin n → (WO S T →₀ ℂ)) (ha : ∀ i, GlobalTheory.FinPl.CombAt (· = pv i) (a i))
    (hb : ∀ i, GlobalTheory.FinPl.CombAt (· = pv i) (b i)) :
    ∀ l : List (Fin n), l.Nodup → ∀ g, l.foldr (fun i g' => comb ψ S T (b i) (comb ψ S T (a i) g')) g =
      l.foldr (fun i g' => comb ψ S T (b i) g') (l.foldr (fun i g' => comb ψ S T (a i) g') g) := by
  have pass : ∀ x (t : List (Fin n)), x ∉ t → ∀ Y, comb ψ S T (a x) (t.foldr (fun i g' => comb ψ S T (b i) g') Y) =
      t.foldr (fun i g' => comb ψ S T (b i) g') (comb ψ S T (a x) Y) := by
    intro x t
    induction t with
    | nil => intro _ Y; rfl
    | cons y t ih =>
      intro hx Y
      have hxy : x ≠ y := fun e => hx (e ▸ List.mem_cons_self)
      have hxt : x ∉ t := fun m => hx (List.mem_cons_of_mem _ m)
      have hd : ∀ p, (· = pv x) p → ¬ (· = pv y) p := fun p h1 h2 => hxy (hv (h1.symm.trans h2))
      simp only [List.foldr_cons]
      rw [(GlobalTheory.DisjComb.main D ψ hψ S T _ _ hd).1 (a x) (b y) (ha x) (hb y), ih hxt]
  intro l
  induction l with
  | nil => intro _ g; rfl
  | cons x t ih =>
    intro hnd g
    rw [List.nodup_cons] at hnd
    simp only [List.foldr_cons]
    rw [ih hnd.2, pass x t hnd.1]

theorem comp_list (hψ : IsStdChar D ψ (-1)) {n : ℕ} (Q : GlobalTheory.FinPl.Pl D → Prop) (a : Fin n → (WO S T →₀ ℂ))
    (ha : ∀ i, GlobalTheory.FinPl.CombAt Q (a i)) : ∀ l : List (Fin n), ∃ o, GlobalTheory.FinPl.CombAt Q o ∧
      ∀ g, comb ψ S T o g = l.foldr (fun i g' => comb ψ S T (a i) g') g := by
  intro l
  induction l with
  | nil =>
    refine ⟨Finsupp.single 0 1, fun u hu => ?_, fun g => ?_⟩
    · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hu
      split_ifs at hu with h0
      · subst h0; exact fun i j => Submodule.zero_mem _
      · exact absurd rfl hu
    · simp only [comb, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
        Finsupp.single_eq_same, one_smul, List.foldr_nil]
      exact GlobalTheory.MixPer.heisO_zero ψ S T g
  | cons x t ih =>
    obtain ⟨o, ho, hc⟩ := ih
    obtain ⟨e, he, hce⟩ := (GlobalTheory.DisjComb.main D ψ hψ S T Q (fun _ => False) (fun _ _ h => h)).2.2.2.1 (a x) o
      (combAt_mono' (fun p hp => Or.inl hp) (ha x)) (combAt_mono' (fun p hp => Or.inl hp) ho)
    refine ⟨e, combAt_mono' (fun p hp => hp.elim id False.elim) he, fun g => ?_⟩
    rw [hce, hc]
    rfl

theorem latV_eq_of_moves {V : HSp D} {g : GA D V} {Λ M N : GlobalTheory.FinPl.Lat V} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hM : Submodule.IsLattice D.host.E M) (hN : Submodule.IsLattice D.host.E N)
    (h1 : GlobalTheory.FinPl.Moves V g Λ M P) (h2 : GlobalTheory.FinPl.Moves V g Λ N P) :
    GlobalTheory.FinPl.latV V M P = GlobalTheory.FinPl.latV V N P := by
  have key : ∀ (A B : GlobalTheory.FinPl.Lat V), Submodule.IsLattice D.host.E A → GlobalTheory.FinPl.Moves V g Λ A P →
      GlobalTheory.FinPl.Moves V g Λ B P → ∀ y, y ∈ GlobalTheory.FinPl.latV V A P → y ∈ GlobalTheory.FinPl.latV V B P := by
    intro A B hA hgA hgB y hy
    have hent : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D P := ((((_root_.GlobalTheory.FinPl.localComponents D P).2 V).2.2.2 A y hA).1 hy).1
    have hz := GlobalTheory.VacMove.mem_ideal_mulVec _ (Formalism.L2.Theta.mt V g⁻¹) y hent
    have e : Formalism.L2.Theta.mt V g *ᵥ (Formalism.L2.Theta.mt V g⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, GlobalTheory.VacMove.mt_mul_inv', Matrix.one_mulVec]
    have h3 := (hgA _ hz).2 (e.symm ▸ hy)
    have h4 := (hgB _ hz).1 h3
    rwa [e] at h4
  ext y
  exact ⟨key M N hM h1 h2 y, key N M hN h2 h1 y⟩

end Gen

end GlobalTheory.DatumTopAt

namespace GlobalTheory.DatumTopAt

end GlobalTheory.DatumTopAt
