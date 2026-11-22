import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj (dualMap FrPt Gx PPx IsCombAt embK)
open scoped CategoryTheory.Obj

section Bundles

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

def GenThrough (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} {φ' : K → (Y' ⟶ X')}
    {φ : K → (Y ⟶ X)} (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) :
    Prop :=
  (∀ k, φ' k ≫ F = h ≫ φ k) ∧ PMaps w φ' φ ε a t h

end Bundles

section Tangent

variable {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A}

abbrev EpsPt (D₀ : Out.DegPre A) : Type := Out.GtPt D₀ (epsR A)

def IsTanGt (ν : EpsPt D₀) : Prop :=
  IsTangent ν.b ∧ ∀ x, LB.Gen.Corr D₀.P.L _ _ _ _
    (LB.pullGen D₀.P.L _ _ (ν.s x) (spMap (TrivSqZeroExt.fstHom A A A).toRingHom)) (LB.oneGen D₀.P.L)

def IsSmulGt (r : A) (ν ν' : EpsPt D₀) : Prop := Out.GtPt.IsPull (spMap (epsMul r)) ν ν'

def IsCombGt {m : ℕ} (ν : Fin m → EpsPt D₀) (r : Fin m → A) (ω : EpsPt D₀) : Prop :=
  ∃ (u : Fin m → EpsPt D₀) (s : Fin (m + 1) → EpsPt D₀), (∀ i, IsSmulGt (r i) (ν i) (u i)) ∧ (s 0).IsZero ∧
    (∀ i : Fin m, Out.GtPt.IsAdd (s i.castSucc) (u i) (s i.succ)) ∧ s (Fin.last m) = ω

def ActGt {O : Type} [CommRing O] [StarRing O] [Module O D₀.X] (oa : D₀.OAct O) {T : Over (Sp A)} (a : O)
    (g g' : Out.GtPt D₀ T) : Prop :=
  g'.b = g.b ≫ oa.onB.act a ∧
    ∀ u : LB.Gen (LB.LinComb D₀.P.L (Out.rosatiφ D₀.P.A (oa.onB.act (star a)) (oa.onB.act a)) Out.rosatiε), u.IsGen →
      LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (Out.zero2 D₀.P.A)) (LB.oneGen D₀.P.L) →
      ∀ x, LB.Gen.Corr D₀.P.L _ _ _ _
        (LB.mulGen D₀.P.L _ _ _ _ (g.s (star a • x))
          (LB.pullGen D₀.P.L _ _ u (lift (Out.DegPre.cT D₀ T x) g.b).left)) (g'.s x)

def IsEigGt {O : Type} [CommRing O] [StarRing O] [Module O D₀.X] (oa : D₀.OAct O) (t : O →+* A) (ν : EpsPt D₀) : Prop :=
  ∀ a : O, ∃ ν' : EpsPt D₀, IsSmulGt (t a) ν ν' ∧ ActGt oa a ν ν'

def IsEigBasisGt {O : Type} [CommRing O] [StarRing O] [Module O D₀.X] (oa : D₀.OAct O) (t : O →+* A) {m : ℕ}
    (ν : Fin m → EpsPt D₀) : Prop :=
  (∀ i, IsTanGt (ν i)) ∧ (∀ i, IsEigGt oa t (ν i)) ∧
    ∀ ω : EpsPt D₀, IsTanGt ω → IsEigGt oa t ω → ∃! r : Fin m → A, IsCombGt ν r ω

end Tangent

section BaseChange

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {g : A →+* A'}
  {D₀ : Out.DegPre A} {D₁ : Out.DegPre A'}

abbrev prOf (pd : Out.IsPullDeg g D₀ D₁) : D₁.P.A.left ⟶ D₀.P.A.left :=
  pd.e.hom.left ≫ pullback.fst D₀.P.A.hom (Out.specOf g)

def fracMap (g : A →+* A') (hg : Function.Injective g) : FractionRing A →+* FractionRing A' :=
  IsFractionRing.lift (g := (algebraMap A' (FractionRing A')).comp g) ((IsFractionRing.injective A' _).comp hg)

def QkBC (pd : Out.IsPullDeg g D₀ D₁) (hg : Function.Injective g) {k : ℕ} (p : Out.QkPt D₀ (FractionRing A) k)
    (p' : Out.QkPt D₁ (FractionRing A') k) : Prop :=
  ∃ q : Out.QkPt D₁ (FractionRing A') k, pd.xe q.y = p.y ∧
    q.g.b.left ≫ prOf pd = spMap (fracMap g hg) ≫ p.g.b.left ∧
    (∀ x, GenThrough pd.w Out.DegPre.gtε (q.g.s x) (p.g.s (pd.xe x)) (spMap (fracMap g hg))) ∧
    Out.QkPt.Equiv D₁ (FractionRing A') q p'

end BaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Inputs

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {b : O →+* A} {b' : O →+* A'}

def IsLetters (a : ArcIn D l β A b) (io : c.F →+* FractionRing A)
    (ν : ∀ τ : E →+* ℂ, Fin (D.mult τ) → EpsPt a.D₀) : Prop :=
  letI := H.starRing
  io.comp β = (algebraMap A (FractionRing A)).comp b ∧
    ∀ τ, ∃ t : 𝓞 E →+* A, (algebraMap A (FractionRing A)).comp t = io.comp (embK c τ) ∧ IsEigBasisGt a.oa t (ν τ)

def InputBC (g : A →+* A') (a : ArcIn D l β A b) (a' : ArcIn D l β A' b') (pd : Out.IsPullDeg g a.D₀ a'.D₀) : Prop :=
  letI := H.starRing
  b' = g.comp b ∧ (∀ (r : 𝓞 E) x, pd.xe (r • x) = r • pd.xe x) ∧
    (∀ r : 𝓞 E, (a'.oa.onB.act r).left ≫ prOf pd = prOf pd ≫ (a.oa.onB.act r).left) ∧
    (∀ x z, a'.be x z = a.be (pd.xe x) (pd.xe z)) ∧
    ∃ hg : Function.Injective g, (∀ v, QkBC pd hg (a.etaA v) (a'.etaA v)) ∧
      ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), QkBC pd hg (a.eta v) (a'.eta v)

abbrev Wit (Y : Model Xo c β) (a : ArcIn D l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) :=
  ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := A)) PowerSeries.X χ

variable {Y : Model Xo c β}

def WitBC (g : A →+* A') {a : ArcIn D l β A b} {a' : ArcIn D l β A' b'} (pd : Out.IsPullDeg g a.D₀ a'.D₀)
    {χ : Sp (PowerSeries A) ⟶ Y.X} {χ' : Sp (PowerSeries A') ⟶ Y.X} (W : Wit Y a χ) (W' : Wit Y a' χ') : Prop :=
  InputBC g a a' pd ∧ χ' = spMap (PowerSeries.map g) ≫ χ ∧
    ∃ (hD : Out.IsPullDeg (PowerSeries.map g) W.P.D.toPre W'.P.D.toPre)
      (bc : W'.t.G ≅ (Over.pullback (Out.specOf (PowerSeries.map g))).obj W.t.G),
      IsMonHom bc.hom ∧ Out.IsPullUnif (PowerSeries.map g) hD bc W.P.U W'.P.U ∧
      W'.m.φ = (bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf (PowerSeries.map g))) ≫ W.m.φ ∧
      W'.φ ≫ prOf pd = prOf hD ≫ W.φ ∧ (∀ x, hD.xe (W'.e x) = W.e (pd.xe x)) ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ W'.P.D.toPre.P.A.left) (z : Z) (j : a.D₀.P.L.ι) (i : W.P.D.toPre.P.L.ι)
        (i' : a'.D₀.P.L.ι) (k : W'.P.D.toPre.P.L.ι), (f ≫ prOf hD ≫ W.φ) z ∈ a.D₀.P.L.U j →
        (f ≫ prOf hD) z ∈ W.P.D.toPre.P.L.U i → (f ≫ W'.φ) z ∈ a'.D₀.P.L.U i' → f z ∈ W'.P.D.toPre.P.L.U k →
        gw W.w (f ≫ prOf hD) z j i * gw hD.w f z i k = gw pd.w (f ≫ W'.φ) z j i' * gw W'.w f z i' k

variable {a : ArcIn D l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X}

variable {S : Type} [CommRing S] [Algebra c.F S]

end Inputs

end GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints
