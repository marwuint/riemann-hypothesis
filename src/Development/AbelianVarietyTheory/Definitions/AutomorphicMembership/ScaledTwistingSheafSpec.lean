import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MeetsOpensOfSeparatesSections
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullGenLBIsGen

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

structure CDiv (X : Scheme.{0}) : Type where

  pos : X.IdealSheafData

  neg : X.IdealSheafData
  pos_cart : FinalTheorems.EffCartier pos
  neg_cart : FinalTheorems.EffCartier neg

namespace CDiv

variable {X X' : Scheme.{0}}

def Eff (B : CDiv X) : Prop := B.pos ≤ B.neg

def ZeroAt (B : CDiv X) (g : X' ⟶ X) (x : X') : Prop := FinalTheorems.stalkId (B.pos.comap g) x = FinalTheorems.stalkId (B.neg.comap g) x

def PosAt (B : CDiv X) (g : X' ⟶ X) (x : X') : Prop := FinalTheorems.stalkId (B.pos.comap g) x < FinalTheorems.stalkId (B.neg.comap g) x

def AmpleTw (B : CDiv X) (g : X' ⟶ X) (L : LB X') : Prop :=
  ∃ C₁ C₂ : EffCartierData X', C₁.idealSheaf = B.pos.comap g ∧ C₂.idealSheaf = B.neg.comap g ∧
    IsAmpleLB (GlobalTheory.CechPic.tens (GlobalTheory.CechPic.tens L C₂.lb) (GlobalTheory.CechPic.dual C₁.lb))

end CDiv

def LogBd {X Q : Scheme.{0}} (D : LB X) (ι : Q ⟶ X) (w : (D.pull ι).Gen) (p : ℕ) (δ : ℝ) : Prop :=
  ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C], ‖(p : C)‖ = (p : ℝ)⁻¹ →
    ∀ (z : Sp ↥(intO C) ⟶ X) (y : Sp C ⟶ Q), y ≫ ι = spMap (intO C).subtype ≫ z → ∀ i : D.ι, ⊤ ≤ z ⁻¹ᵁ D.U i →
      |Real.log ‖valF y _ (w.s fun _ => i).val‖| ≤ δ

def FinLB.pull {X X' : Scheme.{0}} (L : FinLB X) (f : X' ⟶ X) : FinLB X' where
  n := L.n
  U i := (L.lb.pull f).U fun _ => i
  g i k := (L.lb.pull f).g (fun _ => i) fun _ => k
  isLB := have h := LB.isLB_pull L.isLB f
    ⟨top_le_iff.1 (h.cover.ge.trans (iSup_le fun i => le_iSup_of_le (i PUnit.unit) le_rfl)),
      fun _ => h.g_self _, fun _ _ _ => h.cocycle _ _ _⟩

theorem FinLB.lbIso_pull {X X' : Scheme.{0}} (L : FinLB X) (f : X' ⟶ X) : LBIso (L.pull f).lb (L.lb.pull f) :=
  have h := LB.isLB_pull L.isLB f
  LBIso.chartPull (h := 𝟙 X') (A := L.lb.pull f) (B := L.lb.pull f) ⟨fun i _ => i, fun _ _ h => h, fun _ _ _ _ _ => rfl⟩
    ⟨fun i => i, fun _ _ h => h, fun _ _ _ _ _ => rfl⟩ ((GlobalTheory.CechPic.cls_eq_iff h h).1 rfl)

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {l : Level H}

abbrev GModel (Xo : ∀ l : Level H, Moduli Dw l) (c : Coeff l) : Type 1 :=
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo l) c (algebraMap (𝓞 c.F) c.F)

def DomLoc (Y : LocFam Xo) {c : Coeff l} (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Z : GModel Xo c) : Prop :=
  ∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W),
    (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → Dominates Z (Y p W hp hW ⟨l, c, hg p hp⟩) b

structure PreCode (Xo : ∀ l : Level H, Moduli Dw l) (c : Coeff l) : Type where

  n : ℕ

  I : (PSpace (𝓞 c.F) n).IdealSheafData

  j : (Xo l).XF c ⟶ I.subscheme

variable {Y : LocFam Xo} {c : Coeff l} {hg : ∀ p : ℕ, p.Prime → l.GoodAt p}

namespace PreCode

variable (Z : PreCode Xo c)

abbrev X : Scheme.{0} := Z.I.subscheme

def s : Z.X ⟶ Sp (𝓞 c.F) := Z.I.subschemeι ≫ PSpace.str _ Z.n

def Iso (Z' : GModel Xo c) (e : Z'.X ≅ Z.X) : Prop := e.hom ≫ Z.s = Z'.s ∧ Z'.j ≫ e.hom = Z.j

abbrev gen : Scheme.{0} := pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F))

abbrev genι : Z.gen ⟶ Z.X := pullback.fst _ _

abbrev genStr : Z.gen ⟶ Sp c.F := pullback.snd _ _

theorem proj : IsProjOver Z.s := ⟨Z.n, Z.I.subschemeι, inferInstance, rfl⟩

end PreCode

theorem exists_preCode (Z' : GModel Xo c) : ∃ (Z : PreCode Xo c) (e : Z'.X ≅ Z.X), Z.Iso Z' e := by
  obtain ⟨n, i, hi, e⟩ := Z'.proj
  have : IsIso i.toImage := inferInstance
  refine ⟨⟨n, i.ker, Z'.j ≫ i.toImage⟩, asIso i.toImage, ?_, rfl⟩
  change i.toImage ≫ i.imageι ≫ _ = _
  rw [← Category.assoc, i.toImage_imageι, e]

structure Code (Y : LocFam Xo) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) : Type extends PreCode Xo c where
  ex : ∃ (Z' : GModel Xo c) (e : Z'.X ≅ toPreCode.X), toPreCode.Iso Z' e ∧ DomLoc Y hg Z'

theorem exists_code (Z' : GModel Xo c) (h : DomLoc Y hg Z') :
    ∃ (Z : Code Y c hg) (e : Z'.X ≅ Z.X), Z.Iso Z' e := by
  obtain ⟨Z, e, he⟩ := exists_preCode Z'
  exact ⟨⟨Z, Z', e, he, h⟩, e, he⟩

namespace Code

variable (Z : Code Y c hg)

def NoVert (B : CDiv Z.X) : Prop :=
  ∀ x : Z.X, ringKrullDim (Z.X.presheaf.stalk x) = 1 → ¬ CharZero (Z.X.residueField x) → B.ZeroAt (𝟙 _) x

def PosBd (B : CDiv Z.X) : Prop :=
  ∃ (Z' : GModel Xo c) (T : TorModel Z') (g : gen T.Z ⟶ Z.X),
    g ≫ Z.s = genStr T.Z ≫ spMap (algebraMap (𝓞 c.F) c.F) ∧ T.Z.jQ ≫ g = Z.j ∧
    ∀ x : gen T.Z, ringKrullDim ((gen T.Z).presheaf.stalk x) = 1 →
      (x ∈ genBd T.Z → B.PosAt g x) ∧ (x ∉ genBd T.Z → B.ZeroAt g x)

def AmpleHodge (m : ℕ) (B : CDiv Z.X) : Prop :=
  ∃ (Z' : GModel Xo c) (e : Z'.X ≅ Z.X), Z.Iso Z' e ∧ B.AmpleTw e.hom (lbPow (GlobalTheory.FlagMod.detOm Z') m)

section BC

variable {p : ℕ} {W : ValuationSubring ℂ} {hp : p.Prime} {hW : (p : ℂ) ∈ W.nonunits}

def IsBC (Z' : Mdl (Y p W hp hW) ⟨l, c, hg p hp⟩) : Prop :=
  ∃ hi : Z'.i = ⟨l, c, hg p hp⟩, (∀ σ, Z'.ty σ = ∅) ∧
    ∃ (b : 𝓞 c.F →+* Z'.i.c.V W) (ν : Z'.X ⟶ pullback Z.s (spMap b)),
      (∀ x, (((b x : Z'.i.c.V W) : Z'.i.c.F) : ℂ) = ((x : c.F) : ℂ)) ∧ IsFinite ν ∧ ν ≫ pullback.snd _ _ = Z'.s ∧
      pullback.fst Z'.π (Y p W hp hW Z'.i).j ≫ ν ≫ pullback.fst _ _ =
        pullback.snd Z'.π (Y p W hp hW Z'.i).j ≫ eqToHom (congrArg (fun i : Idx H p => (Xo i.l).XF i.c) hi) ≫ Z.j

end BC

end Code

structure QLB (Y : LocFam Xo) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) : Type where

  Z : Code Y c hg

  L : FinLB Z.X

  m : ℕ
  m_pos : 0 < m

namespace QLB

variable (M : QLB Y c hg)

def NefFib : Prop :=
  ∀ (P : Ideal (𝓞 c.F)) [P.IsPrime],
    letI := algebraΓOfHom (pullback.snd M.Z.s (spMap (algebraMap (𝓞 c.F) P.ResidueField)))
    IsNef P.ResidueField (M.L.lb.pull (pullback.fst M.Z.s (spMap (algebraMap (𝓞 c.F) P.ResidueField))))

def AmpleGen : Prop := IsAmpleLB (M.L.lb.pull M.Z.genι)

def LimRA : Prop :=
  ∃ T : Finset ℕ, ∀ ε : ℝ, 0 < ε → ∃ (X' : Scheme.{0}) (b : X' ⟶ M.Z.X) (ι : M.Z.gen ⟶ X') (k : ℕ) (L' : LB X')
    (w : ((LB.div L' (lbPow (M.L.lb.pull b) k)).pull ι).Gen),
    IsProjOver (b ≫ M.Z.s) ∧ Flat (b ≫ M.Z.s) ∧
    IsPullback ι M.Z.genStr (b ≫ M.Z.s) (spMap (algebraMap (𝓞 c.F) c.F)) ∧ ι ≫ b = M.Z.genι ∧
    0 < k ∧ IsAmpleLB L' ∧ w.IsGen ∧
    ∀ p : ℕ, p.Prime → LogBd _ ι w p (if p ∈ T then ε * (k * M.m) else 0)

variable {M}

end QLB

end Free

variable {D : D7} {A : Amb D} {N j : ℕ}

abbrev CodeAt (S : Sig A N j) (κ : Lv A) : Type := Code S.sys.Y κ.c κ.good

def IsBCAt {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p) (Z : CodeAt S κ) (Z' : ct.Mdl) : Prop :=
  Z.IsBC (hp := ct.hp) (hW := ct.hW) Z'

instance nonempty_codeAt (S : Sig A N j) (κ : Lv A) : Nonempty (CodeAt S κ) :=
  (exists_code (Y := S.sys.Y) _ (S.tor.glob κ.l κ.c κ.good).2.1).elim fun Z _ => ⟨Z⟩

end GlobalTheory.ShFam.Pad
