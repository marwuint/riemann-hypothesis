import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.HeightCounting.Up.ThirdAgree

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting.Up.RealOfReading

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem agree_of_data (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) {cf : CharFrame D} {nch : NChoice D}
    (tp : TupTied D cf nch) (hC : R.C = cf) (Xd : DivX D) (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) (hb htup hg hf)
    (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hrep : ∀ σ, (rep σ).Iso (principalLevelFrame.rowRepR R.θ (Y.eFT σ)))
    (c : ∀ i, CoefA (Vc D i)) (hc : R.cV = c) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (std : ∀ i, R3.StdFrame Y.hF (PV i))
    (eW : ∀ μ, Used0 D μ → ∀ i : Fin D.R.m, (M μ (i.1 + 1) (by omega) (by omega)).wt.W ≃ₗ[ℂ] (c i).W)
    (jm : ∀ μ, Used0 D μ → ∀ i : Fin D.R.m, D.what₂.Mt μ (i.1 + 1) → GA D (Vc D i) → (c i).W)
    (hj : ∀ μ h i x, HEq (Y.IL.jMt μ h i x).1 (jm μ h i x))
    (read : ∀ μ (h : Used0 D μ) (i : Fin D.R.m) (x : D.what₂.Mt μ (i.1 + 1)) (g : GAf D.host.E D.R.nV),
      eW μ h i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = jm μ h i x ((PV i).ψ g))
    (rat : ∀ (i : Fin D.R.m) (g : GAf D.host.E D.R.nV), g ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔
      ∃ γ ∈ Formalism.L2.Theta.GQ (Vc D i), finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g))
    (wt : ∀ μ (h : Used0 D μ) (i : Fin D.R.m) (g : ReciprocityTheory.Aut.GQ D.host.E D.R.nV), ∀ γ ∈ Formalism.L2.Theta.GQ (Vc D i),
      finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g) → ∀ v,
        eW μ h i ((M μ (i.1 + 1) (by omega) (by omega)).wt.ρ g v) = (c i).ρ γ (eW μ h i v)) :
    Nonempty (GlobalTheory.NJoin.Agree (realOfRead R.toRealDat F.lv2 Y tp hC Xd E labPi hb htup hg hf) M rep) := by
  subst hc
  refine ⟨⟨Y.hF, PV, fun j => (StandardFrameAgreement.stdFrame_iff _ _).1 (std j), fun j => (StandardFrameAgreement.stdFrame_iff _ _).1 (Y.stdPsi.2 j),
    fun _ => 1, ?_, fun μ hμ j => (eW μ hμ j).symm, ?_, ?_, hrep⟩⟩
  · intro j h
    simp only [inv_one, one_mul, mul_one]
    exact rat j h
  · intro μ hμ j h γ hγ he v
    have he' := he
    simp only [inv_one, one_mul, mul_one] at he'
    have key := wt μ hμ j h γ hγ he' ((eW μ hμ j).symm v)
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    refine Eq.trans ?_ key.symm
    exact congrArg _ (LinearEquiv.apply_symm_apply _ v).symm
  · intro μ hμ j x h
    refine (LinearEquiv.eq_symm_apply _).2 ?_
    refine (read μ hμ j x h).trans ?_
    simp only [inv_one, one_mul]
    exact (congrFun (eq_of_heq (hj μ hμ j x)) _).symm

theorem heq_apply {Mt : D.what₂.Tup → ℕ → Hs} {c c' : ∀ i, CoefA (Vc D i)} (h : c = c')
    (j : ∀ μ (i : Fin D.R.m), (Mt μ ((i : ℕ) + 1)).T →ₗ[ℂ] (GA D (Vc D i) → (c i).W))
    (j' : ∀ μ (i : Fin D.R.m), (Mt μ ((i : ℕ) + 1)).T →ₗ[ℂ] (GA D (Vc D i) → (c' i).W)) (hj : HEq j j') (μ i x) :
    HEq (j μ i x) (j' μ i x) := by
  subst h
  cases hj
  rfl

end Gen

section Copy

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : TwDat B}
  {Wt : Set B.places.Pl}

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Pj.instCMHost (@Late.st B C a).toD7) (@Pj.Par.H (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.l (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.c (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Pj.instCMHost (@Late.st B C a).toD7) (@Pj.Par.H (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.l (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.c (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))

def cpV (c : ∀ i, CoefA (Vc a.D i)) : ∀ i, CoefA (Vc b.D i) := fun i => (by with_unfolding_all exact ((coefA b (c ((by with_unfolding_all exact (i :))))) :))

theorem cV_copy (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (h1 : z.Xg = z₀.Xg) (h2 : z.tr = z₀.tr)
    (h3 : HEq z.core (coreJ b z₀.core)) (h4 : HEq z.R (real3 b (iK := z₀.alg) z₀.R)) : z.R.cV = cpV b z₀.R.cV := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  obtain rfl : core = coreJ b z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg b z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :)))
  subst e
  obtain rfl : R = cpR b z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR b z₀)) :))))
  exact (by with_unfolding_all exact ((Eq.refl (cpV b z₀.R.cV)) :))

theorem cV_two (b' : Late B C) {c₀ : ∀ i, CoefA (Vc a.D i)} {c : ∀ i, CoefA (Vc b.D i)} {c' : ∀ i, CoefA (Vc b'.D i)}
    (h : c = cpV b c₀) (h' : c' = cpV b' c₀) : c' = cpV b' c := by
  subst h h'
  exact (by with_unfolding_all exact ((Eq.refl (cpV b' c₀)) :))

end Copy

section Main

theorem iso_of_eq {Lf : Type} [Field Lf] [NumberField Lf] [IsCMField Lf] {n : ℕ} {π π' : NG.FinTyp Lf n} (h : π = π') : π.Iso π' :=
  h ▸ NG.IsoRep.refl _

end Main

end GlobalTheory.HeightCounting.Up.ThirdAgree

end
