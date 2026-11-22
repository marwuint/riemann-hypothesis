import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUnitOfNorm

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

section Dim

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

theorem generic_dim (A : DatAt Y P) : A.U.A.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
  have := A.t.semi.smooth
  have := A.t.semi.geomConnected
  have d₀ : SmoothOfRelativeDimension (0 + A.U.A.g) (pullback.snd A.t.G.hom (Out.jK A.R)) := by
    have := A.U.A.smoothDim
    have : IsIso A.U.U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map A.U.U.gen.hom))
    rw [show pullback.snd A.t.G.hom (Out.jK A.R) = A.U.U.gen.hom.left ≫ A.U.A.A.hom from (Over.w A.U.U.gen.hom).symm]
    infer_instance
  have d₁ := GenericDim.smoothOfRelativeDimension_of_generic A.R A.t.G _ d₀
  have e : spMap (DatAtCheck.fC A) ≫ A.ι = P.y ≫ Y.jQ ≫ pullback.fst _ _ := by
    refine Eq.trans ?_ P.ext
    rw [← A.fac, ← Category.assoc]
    exact congrArg (· ≫ A.ι) (Spec.map_comp (CommRingCat.ofHom A.f) (CommRingCat.ofHom (intO ↥C.S).subtype))
  have p₁ := (IsPullback.of_hasPullback A.t.G.hom (spMap (DatAtCheck.fC A))).paste_horiz A.m.cart.1
  have p₂ := (IsPullback.of_hasPullback Y.oF.t.G.hom P.y).paste_horiz Y.m.cart.1
  rw [e] at p₁
  have d₂ : SmoothOfRelativeDimension (0 + A.U.A.g) (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) d₁
  have d₃ : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (pullback.snd Y.oF.t.G.hom P.y) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      (ObjDim.smoothOfRelativeDimension Y.oF)
  have d₄ : SmoothOfRelativeDimension (0 + Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))) := by
    rw [← p₁.isoIsPullback_hom_snd _ _ p₂]
    infer_instance
  have : Surjective A.t.G.hom := inferInstance
  obtain ⟨x, -⟩ := (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))).surjective (Per.gen ↥C.S)
  simpa using H1.dim_unique _ d₂ d₄ x

theorem dim_add_rank (A : DatAt Y P) :
    A.U.D.toPre.P.g + Module.finrank ℤ A.Ylat = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
  have h := UT.dim_eq_rank_add_dim firstFiveLaws A.R _ ⟨A.noeth, inferInstance, A.normal, A.complete⟩ A.U.D A.U.A A.t.G
    A.t.semi A.U.U
  rw [← generic_dim A, add_comm]
  exact h.symm

end Dim

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem finrank_host_eq (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

theorem complexConj_eq_conj (D : D7) (x : D.host.E) : IsCMField.complexConj D.host.E x = D.host.conj x := by
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

namespace At

variable (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z)

def beLin : ct.Ylat y →ₗ[ℤ] ct.Ylat y →ₗ[ℤ] ℝ := (ct.dat y).beLin (PointLawsEdge.betaAdd _ p)

def evidence : Per.Reading (ct.dat y) := (Per.nonempty_reading ct.hp.one_lt (ct.dat y)).some

def tauVal (a : ct.Ylat y) (χ : ct.chX y) : ((ct.fld y).C)ˣ := (ct.evidence y).t a ((ct.phi y).symm χ)

def lineShift (a : ct.Ylat y) : ct.chX y := ct.phi y a

def mulFst (a b : ct.Ylat y) : ct.chX y := ct.lineShift y (a + b) - ct.lineShift y a

def mulSnd (a b : ct.Ylat y) : ct.chX y := ct.lineShift y (a + b) - ct.lineShift y b

def mulConst (a b : ct.Ylat y) : ((ct.fld y).C)ˣ :=
  Exists.choose (p := fun t : (↥y.C.S)ˣ => Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) (t : ↥y.C.S))
    ⟨(ct.evidence y).t a b, (ct.evidence y).isVal a b⟩

def abDim : ℕ := (ct.dat y).U.D.toPre.P.g

theorem beLin_apply (a b : ct.Ylat y) : ct.beLin y a b = (ct.dat y).beta a b := rfl

theorem abDim_add : ct.abDim y + Module.finrank ℤ (ct.Ylat y) = D.R.f * N := by
  have h := dim_add_rank (ct.dat y)
  rw [finrank_host_eq, S.rank_eq, Nat.mul_div_cancel_left _ two_pos] at h
  exact h

end At

def motTrue (ct : At S κ p) : MotSt ct where
  be y := ct.beLin y
  be_symm y a b := (ct.dat y).beta_symm a b
  be_bal y c c' h a b := PointLawsEdge.betaBal _ p _ _ (ct.dat y) c c' (h.trans (complexConj_eq_conj D _).symm) a b
  be_posDef y := PointLawsEdge.betaPosDef _ ct.hp.one_lt _ _ (ct.dat y)
  yl_rank y := by
    obtain ⟨ρ, h₁, h₂, h₃⟩ := PointLawsEdge.rank_le (ct.dat y)
    rw [finrank_host_eq, Nat.mul_div_cancel_left _ two_pos] at h₁
    have := S.p_eq
    have := S.rank_eq
    exact ⟨ρ, h₁, fun _ _ => by omega⟩
  psiV y a := vU p (ct.mulConst y a (w0 D • a))
  tau y := ct.tauVal y
  tau_add_left y a a' χ := (ct.evidence y).add_left a a' _
  tau_add_right y a χ χ' := (ct.evidence y).add_right a χ χ'
  tau_symm y a b := (ct.evidence y).symm a b
  tau_smul y c a χ := (ct.evidence y).bal c a χ
  be_tau y a b := (ct.evidence y).beta_eq a b
  multiplicationLatticeFirst y := ct.mulFst y
  multiplicationLatticeSecond y := ct.mulSnd y
  mulC y := ct.mulConst y
  psiV_def _ _ := rfl
  dimB y := ct.abDim y
  dimB_add y := ct.abDim_add y
  be_eq _ _ _ := rfl

end GlobalTheory.LocM
