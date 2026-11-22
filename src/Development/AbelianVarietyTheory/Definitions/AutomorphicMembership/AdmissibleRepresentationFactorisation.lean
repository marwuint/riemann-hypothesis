import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsChartOfMaximal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMemNonunitsOfInduces

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

namespace admitted

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (z : admitted Y i₀)

def stepLB (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : FinLB z.Z.X :=
  match h : letterOf Dw st with
  | some x => (z.line b st x h).L
  | none => FinLB.triv _

theorem stepLB_of_some (b : Bool) {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (h : letterOf Dw st = some x) :
    z.stepLB b st = (z.line b st x h).L := by
  unfold stepLB
  split
  · next y hy => obtain rfl : y = x := Option.some.inj (hy.symm.trans h); rfl
  · next hy => exact absurd (hy.symm.trans h) (by simp)

variable (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)

section Step

variable {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (h : letterOf Dw st = some x)

def genId : GenIso z.Z (z.line false st x h).L (z.line true st x h).L :=
  (exists_isGenId hp hW z.full (GenId.bdd_step hp st) _ _).choose

end Step

variable (d : ℕ) {r : ℕ} {st : Fin r → ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Fin r → Letter Dw}
  (h : ∀ i, letterOf Dw (st i) = some (x i))

def stepPair : DV.FPair (ithOf hp hW z.Z d) r :=
  fpairOf hp hW d (fun i => (z.line false _ _ (h i)).L) (fun i => (z.line true _ _ (h i)).L) fun i => z.genId hp hW (h i)

def dualPair : DV.FPair (ithOf hp hW z.Z d) r :=
  fpairOf hp hW d (fun i => (z.line false _ _ (h i)).L.dual) (fun i => (z.line true _ _ (h i)).L.dual)
    fun i => NModel.GenIso.dual (z.genId hp hW (h i))

theorem pair_x_eq_LB_false (i : Fin r) : (z.stepPair hp hW d h).x i = z.stepLB false (st i) := (z.stepLB_of_some _ _).symm

theorem dualPair_x_eq_dual_LB_false (i : Fin r) : (z.dualPair hp hW d h).x i = (z.stepLB false (st i)).dual :=
  congrArg FinLB.dual (z.stepLB_of_some _ _).symm

omit hp

variable [Fact p.Prime]

include hW

end admitted

section Ranks

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) {p : ℕ} [Fact p.Prime] (jc : DV.KW p →+* ℂ)

theorem comp_cEmb (τ : DV.Emb D p) : jc.comp (DV.cEmb D τ) = conjEmb (jc.comp τ) :=
  RingHom.ext fun x => Formalism.MainNotions.WeightFamilies.emb_conj D (jc.comp τ) x

theorem mult_comp (τ : DV.Emb D p) : S.Dw.mult (jc.comp τ) = DV.rkOf (DV.PsiOf D jc) N j τ := by
  have h₁ := S.p_eq
  have h₂ := S.rank_eq
  by_cases h : τ ∈ DV.PsiOf D jc
  · obtain ⟨t, ht⟩ := id h
    rw [DV.rkOf, if_pos h, ht, Datum.mult, if_pos (A.cm t), h₁]
  · obtain ⟨t, ht⟩ : DV.cEmb D τ ∈ DV.PsiOf D jc := by_contra fun h' => h ((cm_type_meets_conjugate_pair p jc τ).2 h')
    have h₃ := GlobalTheory.Proof.LetterConjugation.mult_add S.Dw (jc.comp τ)
    rw [← comp_cEmb, ht, Datum.mult.eq_1 _ (DV.tauEmb D t), if_pos (A.cm t)] at h₃
    rw [DV.rkOf, if_neg h]
    omega

theorem mult_conj_comp (τ : DV.Emb D p) : S.Dw.mult (conjEmb (jc.comp τ)) = N - DV.rkOf (DV.PsiOf D jc) N j τ := by
  have h₁ := GlobalTheory.Proof.LetterConjugation.mult_add S.Dw (jc.comp τ)
  have h₂ := S.rank_eq
  rw [mult_comp] at h₁
  omega

theorem length_letters : (letters S.Dw).length = D.R.f * N := by
  have h := GlobalTheory.Proof.LetterConjugation.two_mul_length S.Dw
  rw [GlobalTheory.Proof.LetterConjugation.finrank_host, S.rank_eq, mul_assoc] at h
  omega

theorem letterOf_lie (τ : DV.Emb D p) (i : Fin (DV.rkOf (DV.PsiOf D jc) N j τ)) :
    letterOf S.Dw (.inl (jc.comp τ, i)) = some ⟨jc.comp τ, i.cast (mult_comp S jc τ).symm⟩ :=
  dif_pos (i.cast (mult_comp S jc τ).symm).2

theorem letterOf_om (τ : DV.Emb D p) (i : Fin (N - DV.rkOf (DV.PsiOf D jc) N j τ)) :
    letterOf S.Dw (.inl (conjEmb (jc.comp τ), i.rev)) =
      some ⟨conjEmb (jc.comp τ), i.rev.cast (mult_conj_comp S jc τ).symm⟩ :=
  dif_pos (i.rev.cast (mult_conj_comp S jc τ).symm).2

theorem letterOf_whole (k : Fin (D.R.f * N)) :
    letterOf S.Dw (.inr k) = some ((letters S.Dw).get (k.cast (length_letters S).symm)) :=
  List.getElem?_eq_getElem (k.cast (length_letters S).symm).2

end Ranks

section Mdl

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
  {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : DV.KW p →+* ℂ)

def mdlOf : DV.Mdl D p N (DV.rkOf (DV.PsiOf D jc) N j) where
  Z := ithOf hp hW z.Z (Formalism.DegreeFormula.dimFl D.what₂.Tau N)
  cov := cov z
  cov_pos := cov_pos z
  lvl := z.n
  lie τ := z.stepPair hp hW _ (letterOf_lie S jc τ)
  om τ := z.dualPair hp hW _ (letterOf_om S jc τ)
  lieW := z.stepPair hp hW _ (letterOf_whole S)
  omW := z.dualPair hp hW _ fun k => letterOf_whole S k.rev
  om_dual τ := ⟨Fin.revPerm.trans (finCongr (by rw [← mult_conj_comp S, ← mult_comp S, comp_cEmb])), fun i => by
    rw [admitted.dualPair_x_eq_dual_LB_false, admitted.pair_x_eq_LB_false]
    exact (FinLB.firstChern_dual _).trans
      (congrArg (fun σ => -(admitted.stepLB z false (.inl (σ, i.rev))).c1) (comp_cEmb jc τ).symm)⟩
  dim_eq := rfl
  omW_dual := ⟨Fin.revPerm, fun _ => FinLB.firstChern_dual _⟩

variable {jc} {t : D.what₂.Tau} {τ : DV.Emb D p} (ht : jc.comp τ = DV.tauEmb D t)

include ht

end Mdl

section PiLocalization₂

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A)
  (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ))
  (hj : ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la))

theorem one_add_lt_three {p : ℕ} (hp : p.Prime) : 1 + 1 / ((p : ℝ) - 1) < (3 : ℕ) := by
  have h : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : 1 / ((p : ℝ) - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  push_cast
  linarith

abbrev AdmPl (p : ℕ) [Fact p.Prime] (la : PlL D p) : Type :=
  AdmAt S κ Fact.out (placeW_over D p la (jC p la) (hj p la)).1

def admissible_representation_factorisation (hA : AdmEx S κ) : AdmSt D N j jC where
  admitted p _ la := AdmPl S κ jC hj p la
  mdl p _ la z := mdlOf z (jC p la)
  Crv _ _ _ z := Crv z
  deg _ _ _ z c x := degRoot z c (DV.tauEmb D x.1) x.2
  ht p _ _ := (hA p Fact.out _ _ 3 (one_add_lt_three Fact.out)).choose

variable (hA : AdmEx S κ) (p : ℕ) [Fact p.Prime] (la : PlL D p)

end PiLocalization₂

end GlobalTheory.ShFam.Pad
