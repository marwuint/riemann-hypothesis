import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdCopy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntermediateCoefficientPlaceBetweenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormTypeEqAtCorrespondingLiftsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargementStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.StdTr

theorem heq_fin_apply {m m' : ℕ} {f : Fin m → ℕ} {g : Fin m' → ℕ} (h : HEq g f) (hm : m' = m) (i : Fin m) (i' : Fin m')
    (hi : (i : ℕ) = i') : g i' = f i := by
  subst hm
  cases h
  exact congrArg g (Fin.ext hi.symm)

theorem heq_fin_mid {m m' : ℕ} {f : Fin m → ℕ} {g : Fin m' → ℕ} (h : HEq g f) (hm : m' = m) (i : Fin m) (i' : Fin m')
    (hi : (i : ℕ) = i') (k : Fin (f i)) : ∃ k' : Fin (g i'), (k : ℕ) = k' :=
  ⟨⟨k, lt_of_lt_of_eq k.2 (heq_fin_apply h hm i i' hi).symm⟩, rfl⟩

theorem heq_mid {α β : Type} (h : β = α) (a : α) : ∃ b : β, HEq b a := ⟨cast h.symm a, cast_heq _ _⟩

set_option maxHeartbeats 1000000 in

theorem ext_trans {B₁ B₂ B₃ : Base} {f₁ f₂ f₃ T₁ T₂ T₃} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {w₃ : ColW B₃ f₃ T₃} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {Z₃ : w₃.Lt} {h₁ h₂ h₃ W₁ W₂ W₃} {z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁} {z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂} {z₃ : Dat (w₃.st Z₃) w₃.I h₃ T₃ W₃} (e₁₂ : Enl B₁ B₂) (e₂₃ : Enl B₂ B₃) (x : Ext z₁ z₂) (y : Ext z₂ z₃) :
    Ext z₁ z₃ := by
  have hmm : (w₂.st Z₂).toD7.R.m = (w₁.st Z₁).toD7.R.m := congrArg (fun P : Pre => P.R.m) e₁₂.1
  have hm : ∀ i : Fin (w₁.st Z₁).toD7.R.m, ∃ i' : Fin (w₂.st Z₂).toD7.R.m, (i : ℕ) = i' :=
    fun i => ⟨⟨i, lt_of_lt_of_eq i.2 hmm.symm⟩, rfl⟩
  refine @Ext.mk B₁ B₃ f₁ f₃ T₁ T₃ w₁ w₃ Z₁ Z₃ h₁ h₃ W₁ W₃ z₁ z₃ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact y.H.trans x.H
  · exact y.l.trans x.l
  · exact y.c.trans x.c
  · exact y.Dw.trans x.Dw
  · exact y.Xo.trans x.Xo
  · exact y.U.trans x.U
  · exact y.V.trans x.V
  · exact y.dict.trans x.dict
  · exact y.mu.trans x.mu
  · exact y.Kf.trans x.Kf
  · exact y.cE.trans x.cE
  · exact y.chiW.trans x.chiW
  · exact y.x₀.trans x.x₀
  · exact y.iota.trans x.iota
  · exact y.ψ.trans x.ψ
  · exact y.θ.trans x.θ
  · exact y.βW.trans x.βW
  · exact y.βY.trans x.βY
  · exact y.nW.trans x.nW
  · exact y.βV.trans x.βV
  · exact y.ΛV.trans x.ΛV
  · exact y.ΛW.trans x.ΛW
  · exact y.Pg.trans x.Pg
  · exact y.eG.trans x.eG
  · exact y.Sb.trans x.Sb
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.BV i i' hi'
    have b := y.BV i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact b.1.trans a.1
    refine And.intro ?_ ?_
    · exact b.2.1.trans a.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.1.trans a.2.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.2.1.trans a.2.2.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.2.2.1.trans a.2.2.2.2.1
    exact b.2.2.2.2.2.trans a.2.2.2.2.2
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.MW i i' hi'
    have b := y.MW i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact b.1.trans a.1
    refine And.intro ?_ ?_
    · exact b.2.1.trans a.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.1.trans a.2.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.2.1.trans a.2.2.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.2.2.1.trans a.2.2.2.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.2.2.2.1.trans a.2.2.2.2.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.2.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.2.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.2.2.2.1
    intro φ φ'' hφ
    refine Exists.elim (heq_mid (GlobalTheory.T.cuspFormType_eq_at_corresponding_lifts z₁ z₂ e₁₂ x i i' hi') φ) fun φ' hφ' => ?_
    with_unfolding_all exact (HEq.trans (b.2.2.2.2.2.2.2.2.2.2 φ' φ'' (HEq.trans hφ hφ'.symm)) (a.2.2.2.2.2.2.2.2.2.2 φ φ' hφ') :)
  · intro i i'' h φ φ'' hφ k k'' hk
    refine Exists.elim (hm i) fun i' hi' => ?_
    refine Exists.elim (heq_mid (GlobalTheory.T.cuspFormType_eq_at_corresponding_lifts z₁ z₂ e₁₂ x i i' hi') φ) fun φ' hφ' => ?_
    refine Exists.elim (heq_fin_mid x.nW hmm i i' hi' k) fun k' hk' => ?_
    with_unfolding_all exact (Eq.trans (y.forms i' i'' (hi'.symm.trans h) φ' φ'' (HEq.trans hφ hφ'.symm) k' k'' (hk'.symm.trans hk)) (x.forms i i' hi' φ φ' hφ' k k' hk') :)
  · intro v v'' hB
    refine Exists.elim (GlobalTheory.T.exists_intermediate_coefficientPlace_between (w₁.D Z₁) (w₂.D Z₂) (w₃.D Z₃) e₂₃.2.2.2 v v'' hB) fun v' h => ?_
    with_unfolding_all exact (Iff.trans (x.W1 v v' h.1) (y.W1 v' v'' h.2) :)
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.cV i i' hi'
    have b := y.cV i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact b.1.trans a.1
    exact b.2.trans a.2
  · exact y.pb.trans x.pb
  · exact y.ΛY.trans x.ΛY
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.κ i i' hi'
    have b := y.κ i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact b.1.trans a.1
    refine And.intro ?_ ?_
    · exact b.2.1.trans a.2.1
    exact b.2.2.trans a.2.2
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.ref i i' hi'
    have b := y.ref i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact b.1.trans a.1
    refine And.intro ?_ ?_
    · exact b.2.1.trans a.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.1.trans a.2.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.2.1.trans a.2.2.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.2.2.1.trans a.2.2.2.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.2.2.2.1.trans a.2.2.2.2.2.1
    refine And.intro ?_ ?_
    · exact b.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.1
    exact b.2.2.2.2.2.2.2.trans a.2.2.2.2.2.2.2
  · intro i i'' h ok ok'' φ φ'' C
    refine Exists.elim (hm i) fun i' hi' => ?_
    have hv : HEq (B₂.primes w₂.px).vGs (B₁.primes w₁.px).vGs := by
      have a := heq_of_eq z₂.lev.Pg.symm
      have b := heq_of_eq z₁.lev.Pg
      with_unfolding_all exact (HEq.trans (HEq.trans a x.Pg) b :)
    have L := GlobalTheory.T.referenceTupleLiftForms_pass_to_coeffEnlargement w₁ w₂ W₁ W₂ e₁₂ hv (GlobalTheory.T.tameCharacters_typePrimes_eq_of_extension z₁ z₂ e₁₂ x) ((i : ℕ) + 1) ((i' : ℕ) + 1) (congrArg (· + 1) hi')
    refine Exists.elim (L.2 φ) fun φ' C' => ?_
    have ok' : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 ((i' : ℕ) + 1)).Ok := Formalism.L2.Col.mtKOk _ _ _ _ h₂ _
    have a := x.jL i i' hi' ok ok' φ φ' C'
    have b := y.jL i' i'' (hi'.symm.trans h) ok' ok'' φ' φ'' fun d' d'' hd => by
      refine Exists.elim (heq_mid L.1.symm d') fun d hd' => ?_
      with_unfolding_all exact (HEq.trans (C d d'' (HEq.trans hd hd'.symm)) (HEq.symm (C' d d' hd'.symm)) :)
    with_unfolding_all exact (HEq.trans b a :)

theorem std_copy_and_ext_trans : (∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w.st Z') w.I hX T Wt), z'.Xg = z.Xg → z'.tr = z.tr → HEq z'.R (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := z.alg) z.R) → HEq z'.core (coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ z.core) → z.Std → z'.Std) ∧ ∀ (B₁ B₂ B₃ : Base) f₁ f₂ f₃ T₁ T₂ T₃ (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (w₃ : ColW B₃ f₃ T₃) (Z₁ : w₁.Lt) (Z₂ : w₂.Lt) (Z₃ : w₃.Lt) h₁ h₂ h₃ W₁ W₂ W₃ (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂) (z₃ : Dat (w₃.st Z₃) w₃.I h₃ T₃ W₃), Enl B₁ B₂ → Enl B₂ B₃ → Ext z₁ z₂ → Ext z₂ z₃ → Ext z₁ z₃ :=
  ⟨std_copy, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁₂ e₂₃ x y => ext_trans e₁₂ e₂₃ x y⟩

end GlobalTheory.Mem.R3.Rw.StdTr
