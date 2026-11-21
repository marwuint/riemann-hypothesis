import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchAtType
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocXiEqMulMidXi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyColCh
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiStdEqConstMulLocXi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationTwist

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel

set_option maxHeartbeats 1000000

namespace GlobalTheory.Fam.TopLoc

theorem locTop_eq_of_type : ∀ {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S S' : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S) (mu' : Formalism.L2.DIV.Tup X.F X.E X.K S')
   (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (cst' : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu')) (P : Formalism.L2.Col.rowSG Pr sel mu) (P' : Formalism.L2.Col.rowSG Pr sel mu'),
   P.1 = P'.1 → P.1 ∈ Pr.vGs → cst.sharp = cst'.sharp →
   (∀ a, Formalism.L2.Col.IntAt P.1 a → cst.psi P (a / (Formalism.L2.Col.qOf P.1 : X.E)) = Formalism.L2.Col.psi0P Ch P.1 (Formalism.L2.Col.redP P.1 a)) →
   (∀ a, Formalism.L2.Col.IntAt P'.1 a → cst'.psi P' (a / (Formalism.L2.Col.qOf P'.1 : X.E)) = Formalism.L2.Col.psi0P Ch P'.1 (Formalism.L2.Col.redP P'.1 a)) →
   ∀ m2 y y', (∀ i, Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.qOf P.1 : X.E) * y' i)) →
     GlobalTheory.TopStep.locTop Ch sel mu cst m2 P y y' = GlobalTheory.TopStep.locTop Ch sel mu' cst' m2 P' y y' := by
  intro X Pr R Ch sel S S' mu mu' cst cst' P P' hPP hmem hsh hpsi hpsi' m2 y y' hy
  have hmem' : P'.1 ∈ Pr.vGs := hPP ▸ hmem
  unfold GlobalTheory.TopStep.locTop Formalism.L2.Col.PhiTop Formalism.L2.Col.ftY
  rw [if_pos hmem, if_pos hmem', hsh, if_pos hmem, if_pos hmem', ← hPP]
  congr 1
  split_ifs with hη
  · set η := Formalism.L2.Col.atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y with hηdef
    have hq : ((Formalism.L2.Col.qOf P.1 : ℕ) : X.E) ≠ 0 :=
      Nat.cast_ne_zero.2 fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    have hsum : η ((Formalism.L2.Col.qOf P.1 : X.E) • y') = ∑ i, ((Formalism.L2.Col.qOf P.1 : X.E) * y' i) * η (Pi.single i 1) := by
      conv_lhs => rw [pi_eq_sum_univ' ((Formalism.L2.Col.qOf P.1 : X.E) • y'), map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, Pi.smul_apply, smul_eq_mul]
    have hε : Formalism.L2.Col.IntAt P.1 (Formalism.L2.Col.epsSg : X.E) := by
      simpa [Formalism.L2.Col.epsSg] using Formalism.L2.Col.IntAt.coe P.1 (-1)
    have hint : Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.epsSg : X.E) * η ((Formalism.L2.Col.qOf P.1 : X.E) • y')) := by
      refine hε.mul ?_
      rw [hsum]
      exact GlobalTheory.TopStep.intAt_sum _ fun i _ => (hy i).mul (hη i)
    have hb : (Formalism.L2.Col.epsSg : X.E) * η y' = (Formalism.L2.Col.epsSg : X.E) * η ((Formalism.L2.Col.qOf P.1 : X.E) • y') / (Formalism.L2.Col.qOf P.1 : X.E) := by
      rw [map_smul, smul_eq_mul]; field_simp
    have e1 := hpsi _ hint
    have e2 := hpsi' _ (hPP ▸ hint)
    rw [← hPP] at e2
    rw [hb, e1, e2]
  · rfl

section Normal
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SymChain GlobalTheory.SymChain.UnifChange GlobalTheory.Fam.MidLoc

theorem exists_normal_top {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s κ : ℕ} (S : SymData k s κ) (ϖ' : kˣ) (h : valuation k ((ϖ' : k) - (S.ϖ : k)) < valuation k (S.ϖ : k)) (τ : ℕ) :
    ∃ S' : SymData k s κ, S'.ϖ = ϖ' ∧ S'.ψ = S.ψ ∧ (∀ j, j ≤ s + 2 → S'.μ j = S.μ j) ∧
      (∀ j, s + 2 < j → S'.μ j = 1) ∧ (S'.T (Fin τ)).PhiTop = (S.T (Fin τ)).PhiTop := by
  let S₁ : SymData k s κ :=
    { S with ϖ := ϖ', unif := isUnif_of_near S.unif h, sym := isSymLevel_of_near S.cond S.unif h S.sym }
  have hTop : (S₁.T (Fin τ)).PhiTop = (S.T (Fin τ)).PhiTop :=
    transport_iterPhi S.P S.μ S.tame (s + 1) (near_refl _) (near_typeFrame h _)
  let μ : ℕ → kˣ →* ℂˣ := fun j => if j ≤ s + 2 then S₁.μ j else 1
  have ht : ∀ j, IsTame (μ j) := fun j => by
    simp only [μ]
    split_ifs
    · exact S₁.tame j
    · exact fun _ _ => rfl
  have e : ∀ j, 1 ≤ j → j ≤ s + 2 → μ j = S₁.μ j := fun j _ hj => if_pos hj
  exact ⟨withMu S₁ μ ht, rfl, rfl, fun j hj => if_pos hj, fun j hj => if_neg (by omega),
    (withMu_le S₁ μ ht e (Fin τ)).2.1.trans hTop⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}

end Normal

end GlobalTheory.Fam.TopLoc
