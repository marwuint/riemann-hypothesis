import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SatakeDualWeyl.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

noncomputable section

namespace Formalism.MainNotions.JumpSetsAlt

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.UG TensorProduct Finset NumberField IsDedekindDomain

def Uv {N : ℕ} (lam : DomWeight N) : Fin N → ℤ := fun i => lam.w i + ((N : ℤ) - 1 - (i : ℤ))

def primeTo (l : ℕ) : Submonoid ℤ where
  carrier := {n | IsCoprime n (l : ℤ)}
  one_mem' := isCoprime_one_left
  mul_mem' := fun ha hb => IsCoprime.mul_left ha hb

abbrev Zl (l : ℕ) : Type := Localization (primeTo l)

def ex {N : ℕ} (l : ℕ) (lam : DomWeight N) : ℕ :=
  sInf {J : ℕ | ∀ f ∈ nablaSq (Zl l) N lam, ((l : Zl l) ^ J) • f ∈ delSq (Zl l) N lam}

def restr {N : ℕ} (lam : DomWeight N) (a n : ℕ) (h : a + n ≤ N) : DomWeight n where
  w := fun i => lam.w ⟨a + i, by omega⟩
  anti := by
    intro i j hij
    apply lam.anti
    show a + (i : ℕ) ≤ a + (j : ℕ)
    have : (i : ℕ) ≤ j := hij
    omega

def topRows {N : ℕ} (lam : DomWeight N) (a : ℕ) : DomWeight (min a N) :=
  restr lam 0 (min a N) (by omega)

def botRows {N : ℕ} (lam : DomWeight N) (a : ℕ) : DomWeight (N - a) :=
  restr lam (min a N) (N - a) (by omega)

def RowsWidth {N : ℕ} (U : Fin N → ℤ) (a : ℕ) (w : ℤ) : Prop :=
  ∃ lo : ℤ, ∀ i : Fin N, a ≤ (i : ℕ) → lo ≤ U i ∧ U i ≤ lo + w

def Width {N : ℕ} (U : Fin N → ℤ) (w : ℝ) : Prop :=
  ∃ lo : ℝ, ∀ i : Fin N, lo ≤ (U i : ℝ) ∧ (U i : ℝ) ≤ lo + w

def kap (h l : ℕ) : ℕ := h / (l - 1)

structure ShapeData where
  j : ℕ
  q : ℕ
  xm : ℤ
  xp : ℤ
  maxB : ℤ

def HasShape {N : ℕ} (kc t m : ℕ) (U : Fin N → ℤ) (sh : ShapeData) : Prop :=
  kc + sh.j + t + sh.q = N ∧ sh.j + sh.q ≤ m ∧
  (∀ i : Fin N, (i : ℕ) < kc → sh.xm ≤ U i ∧ U i ≤ sh.xp) ∧
  (∀ i : Fin N, kc + sh.j ≤ (i : ℕ) → (i : ℕ) < kc + sh.j + t →
    U i = sh.maxB - ((i : ℕ) - (kc + sh.j) : ℕ))

def IsLow (kc t : ℕ) (sh : ShapeData) (i : ℕ) : Prop :=
  kc ≤ i ∧ ¬ (kc + sh.j ≤ i ∧ i < kc + sh.j + t)

def blockSet (t : ℕ) (maxB : ℤ) : Finset ℤ := (Finset.range t).image fun s : ℕ => maxB - (s : ℤ)

def mwOf (Us Bs : Finset ℤ) (lo hi : ℤ) (l κ : ℕ) : ℕ := by
  classical
  exact ((Us \ Bs).filter fun u => ∃ x ∈ Finset.Icc (lo - κ) (hi + κ), (l : ℤ) ∣ u - x).card

def Il (xm xp maxB : ℤ) (l : ℕ) : ℝ := by
  classical
  exact if ∃ y ∈ Finset.Icc xm xp, (l : ℤ) ∣ y - maxB then 1 else 0

def d0 (xm maxB : ℤ) (l : ℕ) : ℕ := sInf {d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ xm - (d : ℤ) - maxB}

def embG (D : D7) (τ : D.what₂.Tau) : D.R.GG := DV.toGG D (Sum.inl τ)

def wAt {D : D7} (h : ℕ) (u : D.what₂.Tau → ℤ) : DV.EmbC D → ℤ
  | Sum.inl τ => u τ
  | Sum.inr τ => (h : ℤ) - u τ

def epE {D : D7} (e : Bool) (σ : DV.EmbC D) : DV.EmbC D := if e then σ.swap else σ

def prevE (D : D7) (l : ℕ) (σ : DV.EmbC D) : DV.EmbC D := DV.frobEmb D l 1 σ

def mwE (D : D7) (t h l : ℕ) (U : D.what₂.Tau → Fin D.R.nV → ℤ) (sh : D.what₂.Tau → ShapeData) :
    DV.EmbC D → ℕ
  | Sum.inl τ =>
      mwOf (Finset.univ.image (U τ)) (blockSet t (sh τ).maxB) ((sh τ).maxB - t + 1) (sh τ).maxB l
        (kap h l)
  | Sum.inr τ =>
      mwOf (Finset.univ.image fun i => (h : ℤ) - U τ i)
        ((blockSet t (sh τ).maxB).image fun x => (h : ℤ) - x)
        ((h : ℤ) - (sh τ).maxB) ((h : ℤ) - (sh τ).maxB + t - 1) l (kap h l)

def mw (D : D7) (t h l : ℕ) (U : D.what₂.Tau → Fin D.R.nV → ℤ) (sh : D.what₂.Tau → ShapeData)
    (τ : D.what₂.Tau) : ℕ := mwE D t h l U sh (Sum.inl τ)

def mwF (D : D7) (t h l : ℕ) (U : D.what₂.Tau → Fin D.R.nV → ℤ) (sh : D.what₂.Tau → ShapeData)
    (τ : D.what₂.Tau) : ℕ := mwE D t h l U sh (prevE D l (Sum.inl τ))

abbrev AmbT (R : Type) [CommRing R] (ι : Type) (N : ℕ) : Type :=
  PiTensorProduct R (fun _ : ι => MvPolynomial (Fin N × Fin N) R)

def tensSub {R : Type} [CommRing R] {ι : Type} {N : ℕ}
    (A : ι → Submodule R (MvPolynomial (Fin N × Fin N) R)) : Submodule R (AmbT R ι N) :=
  LinearMap.range (PiTensorProduct.map fun i => (A i).subtype)

def kCl (D : D7) : ℕ := D.R.k - 1

abbrev Cg (R : Type) [CommRing R] (ι : Type) (N : ℕ) : Type := (ι → GL (Fin N) R) × Rˣ

abbrev GE (D : D7) : Type := D.nd.Om ≃ₐ[D.host.E] D.nd.Om

abbrev Ob (l : ℕ) [Fact l.Prime] : ValuationSubring (Om l) :=
  (Valued.v (R := Om l) (Γ₀ := NNReal)).valuationSubring

abbrev kb (l : ℕ) [Fact l.Prime] : Type := IsLocalRing.ResidueField (Ob l)

abbrev ResRep (D : D7) (l : ℕ) [Fact l.Prime] : Type := GE D → Polynomial (kb l)

def cpol {D : D7} {l : ℕ} [Fact l.Prime] {n : ℕ} (ρ : GE D →* GL (Fin n) (kb l)) : ResRep D l :=
  fun g => ((ρ g : GL (Fin n) (kb l)) : Matrix (Fin n) (Fin n) (kb l)).charpoly

def redR {D : D7} {l : ℕ} [Fact l.Prime] {n : ℕ} (r : GE D →* GL (Fin n) (Ob l)) :
    GE D →* GL (Fin n) (kb l) :=
  (Matrix.GeneralLinearGroup.map (IsLocalRing.residue (Ob l))).comp r

abbrev DecW (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) : Subgroup (GE D) :=
  ReciprocityTheory.Gal.Dec (F := D.host.E) (D.nd.plOm.1 w)

def JumpsAre {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) {n : ℕ} (u : Fin n → ℤ) : Prop :=
  ∀ a : ℤ, Module.finrank ↥LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.FildR (P.PD K) T.ρ τ a) =
    Module.finrank ↥LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.FildR (P.PD K) T.ρ τ (a + 1)) +
      (Finset.univ.filter fun i => u i = a).card

structure Prov (D : D7) where

  O : ℕ → Type
  [instO : ∀ l, CommRing (O l)]
  [domO : ∀ l, IsDomain (O l)]
  [dvrO : ∀ l, IsDiscreteValuationRing (O l)]
  [czO : ∀ l, CharZero (O l)]
  [algZ : ∀ (l : ℕ) [Fact l.Prime], Algebra ℤ_[l] (O l)]
  [topO : ∀ l, TopologicalSpace (O l)]

  l_mem : ∀ l, l.Prime → ((l : ℕ) : O l) ∈ IsLocalRing.maximalIdeal (O l)

  fin_l : ∀ l, l.Prime → Finite (O l ⧸ Ideal.span {((l : ℕ) : O l)})

  Gf : Type
  [instGf : Group Gf]
  Gam : Subgroup Gf

  gamE : Gam →* GL (Fin D.R.nV) D.host.E
  gamE_inj : Function.Injective gamE

  Lev : ℕ → Type

  hyp : ∀ l, Lev l → Prop
  Kl : ∀ l, Lev l → Subgroup Gf

  fin_class : ∀ l (c : Lev l), Finite (ClassSet Gam (Kl l c))

  fin_stab : ∀ l (c : Lev l) (g : Gf), (stabAt Gam (Kl l c) g).Finite

  kapK : ∀ l (c : Lev l), Kl l c →* (D.what₂.Tau → GL (Fin D.R.nV) (O l))

  typ : ∀ l (c : Lev l), Kl l c →* (O l)ˣ

  cf : ∀ l (_lam : D.what₂.Tau → DomWeight D.R.nV),
    Representation (O l) (Cg (O l) D.what₂.Tau D.R.nV) (AmbT (O l) D.what₂.Tau D.R.nV)

  cf_def : ∀ l (lam : D.what₂.Tau → DomWeight D.R.nV) (γ : Cg (O l) D.what₂.Tau D.R.nV)
    (x : D.what₂.Tau → MvPolynomial (Fin D.R.nV × Fin D.R.nV) (O l)),
    cf l lam γ (PiTensorProduct.tprod (O l) x) =
      ((γ.2 : (O l)ˣ) : O l) •
        PiTensorProduct.tprod (O l) (fun τ => roundAct (O l) D.R.nV (lam τ) (γ.1 τ) (x τ))

  Hk : ∀ l, Lev l → Type
  [instHk : ∀ l c, CommRing (Hk l c)]
  [algHk : ∀ l c, Algebra (O l) (Hk l c)]
  [modHk : ∀ l c (A : Type) [AddCommGroup A] [Module (O l) A]
    (ρ : Representation (O l) (Cg (O l) D.what₂.Tau D.R.nV) A),
    Module (Hk l c) (AMFK (O l) Gam (Kl l c) (MonoidHom.comp ρ ((kapK l c).prod (typ l c))))]
  [towHk : ∀ l c (A : Type) [AddCommGroup A] [Module (O l) A]
    (ρ : Representation (O l) (Cg (O l) D.what₂.Tau D.R.nV) A),
    IsScalarTower (O l) (Hk l c)
      (AMFK (O l) Gam (Kl l c) (MonoidHom.comp ρ ((kapK l c).prod (typ l c))))]

  hk_transl : ∀ l (c : Lev l) (T : Hk l c), ∃ el : Gf →₀ O l,
    ∀ (A : Type) [AddCommGroup A] [Module (O l) A]
      (ρ : Representation (O l) (Cg (O l) D.what₂.Tau D.R.nV) A)
      (f : AMFK (O l) Gam (Kl l c) (MonoidHom.comp ρ ((kapK l c).prod (typ l c)))) (g : Gf),
      ((T • f : AMFK (O l) Gam (Kl l c) (MonoidHom.comp ρ ((kapK l c).prod (typ l c)))) : Gf → A) g =
        el.sum fun x a => a • (f : Gf → A) (g * x)

  bw : ∀ (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l →
    LocBridge l D.host.E D.nd.Om (ReciprocityTheory.Gal.Dec (F := D.host.E) (D.nd.plOm.1 w)) (O l)

  iota : ∀ (l : ℕ) [Fact l.Prime], D.host.E →+* Om l

  ep : ℕ → Bool

  attached : ∀ (l : ℕ) [Fact l.Prime] (_h : ℕ) (c : Lev l), Ideal (Hk l c) → ResRep D l → Prop

attribute [instance] Prov.instO Prov.domO Prov.dvrO Prov.czO Prov.algZ Prov.topO Prov.instGf Prov.instHk Prov.algHk
  Prov.modHk Prov.towHk

variable {D : D7}

abbrev piK (X : Prov D) (l : ℕ) (c : X.Lev l) : X.Kl l c →* Cg (X.O l) D.what₂.Tau D.R.nV :=
  (X.kapK l c).prod (X.typ l c)

abbrev rho (X : Prov D) (l : ℕ) (c : X.Lev l) (lam : D.what₂.Tau → DomWeight D.R.nV) :
    Representation (X.O l) (X.Kl l c) (AmbT (X.O l) D.what₂.Tau D.R.nV) :=
  MonoidHom.comp (X.cf l lam) (piK X l c)

abbrev Frm (X : Prov D) (l : ℕ) (c : X.Lev l) (lam : D.what₂.Tau → DomWeight D.R.nV) :
    Submodule (X.O l) (X.Gf → AmbT (X.O l) D.what₂.Tau D.R.nV) :=
  AMFK (X.O l) X.Gam (X.Kl l c) (rho X l c lam)

def formsSub (X : Prov D) (l : ℕ) (c : X.Lev l) (lam : D.what₂.Tau → DomWeight D.R.nV)
    (U : Submodule (X.O l) (AmbT (X.O l) D.what₂.Tau D.R.nV)) :
    Submodule (X.Hk l c) (Frm X l c lam) where
  carrier := {f | ∀ g, (f : X.Gf → AmbT (X.O l) D.what₂.Tau D.R.nV) g ∈ U}
  add_mem' := by
    intro a b ha hb g
    exact add_mem (ha g) (hb g)
  zero_mem' := by
    intro g
    exact zero_mem _
  smul_mem' := by
    intro T f hf g
    obtain ⟨el, hel⟩ := X.hk_transl l c T
    rw [hel _ (X.cf l lam) f g]
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hf _)

def MNsub (X : Prov D) (l : ℕ) (c : X.Lev l) (lam : D.what₂.Tau → DomWeight D.R.nV) :
    Submodule (X.Hk l c) (Frm X l c lam) :=
  formsSub X l c lam (tensSub fun τ => nablaSq (X.O l) D.R.nV (lam τ))

def MDsub (X : Prov D) (l : ℕ) (c : X.Lev l) (lam : D.what₂.Tau → DomWeight D.R.nV) :
    Submodule (X.Hk l c) (Frm X l c lam) :=
  formsSub X l c lam (tensSub fun τ => delSq (X.O l) D.R.nV (lam τ))

def MN (X : Prov D) (l : ℕ) (c : X.Lev l) (lam : D.what₂.Tau → DomWeight D.R.nV) :
    Set (Frm X l c lam) := (MNsub X l c lam : Set (Frm X l c lam))

def MD (X : Prov D) (l : ℕ) (c : X.Lev l) (lam : D.what₂.Tau → DomWeight D.R.nV) :
    Set (Frm X l c lam) := (MDsub X l c lam : Set (Frm X l c lam))

def locSet {T M : Type} [CommRing T] [AddCommGroup M] [Module T M] (S : Submonoid T) (N : Set M) :
    Set (LocalizedModule S M) :=
  {y | ∃ x ∈ N, ∃ s : S, LocalizedModule.mk x s = y}

def Incl (X : Prov D) (l : ℕ) (c : X.Lev l) (lam : D.what₂.Tau → DomWeight D.R.nV)
    (mt : Ideal (X.Hk l c)) [mt.IsPrime] (J : ℕ) : Prop :=
  ∀ y ∈ locSet mt.primeCompl (MN X l c lam),
    (algebraMap (X.O l) (X.Hk l c) (((l : ℕ) : X.O l) ^ J)) • y ∈ locSet mt.primeCompl (MD X l c lam)

def JA (D : D7) (l : ℕ) (lam : D.what₂.Tau → DomWeight D.R.nV) : ℕ := ∑ τ, ex l (lam τ)

def RealisesW (X : Prov D) (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E l) (LL : FinExt l)
    (T : LocLat ↥(GK (X.bw l w hw).Kw) ℚ_[l] ↥LL.1 ↥(OL LL)) {n : ℕ} (r : ↥(DecW D w) →* GL (Fin n) (Ob l)) : Prop :=
  ∃ b : Fin n → T.V, LinearIndependent ↥LL.1 b ∧ T.L.T = Submodule.span ↥(OL LL) (Set.range b) ∧
    ∀ (g : ↥(DecW D w)) (j : Fin n), ∃ c : Fin n → ↥(OL LL),
      (∀ i, (((c i : ↥(OL LL)) : ↥LL.1) : Om l) =
        (((r g : GL (Fin n) (Ob l)) : Matrix (Fin n) (Fin n) (Ob l)) i j : Om l)) ∧
      T.ρ ((X.bw l w hw).e g) (b j) = ∑ i, c i • b i

def OverE (X : Prov D) (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E l) (LL : FinExt l) (σ : DV.EmbC D)
    (τ : ↥(X.bw l w hw).Kw.1 →ₐ[ℚ_[l]] ↥LL.1) : Prop :=
  ∀ x : D.host.E,
    ((τ ⟨(X.bw l w hw).j (algebraMap D.host.E D.nd.Om x), (X.bw l w hw).j_E x⟩ : ↥LL.1) : Om l) =
      X.iota l (D.host.sigmaOf (DV.toGG D σ) x)

def CrysAt (X : Prov D) (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E l) {n : ℕ} (r : ↥(DecW D w) →* GL (Fin n) (Ob l))
    (Wt : DV.EmbC D → Fin n → ℤ) : Prop :=
  ∃ (LL : FinExt l) (_ : CaseA (X.bw l w hw).Kw LL)
    (T : LocLat ↥(GK (X.bw l w hw).Kw) ℚ_[l] ↥LL.1 ↥(OL LL)),
    RealisesW X l w hw LL T r ∧ Formalism.WeaklyAdmissibleFiltrations.IsCrys ((D.loc l).PD (X.bw l w hw).Kw) T.ρ ∧
    ∀ σ τ, OverE X l w hw LL σ τ → JumpsAre (D.loc l) T τ (Wt σ)

def crysRepE (X : Prov D) (l : ℕ) [Fact l.Prime] {n : ℕ} (Wt : DV.EmbC D → Fin n → ℤ) :
    Set (ResRep D l) :=
  {P | ∃ r : GE D →* GL (Fin n) (Ob l), P = cpol (redR r) ∧
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E l),
      CrysAt X l w hw (r.comp (DecW D w).subtype) Wt}

def crysRep (X : Prov D) (l : ℕ) [Fact l.Prime] (h : ℕ) {n : ℕ} (U' : D.what₂.Tau → Fin n → ℤ) :
    Set (ResRep D l) :=
  crysRepE X l (fun σ i => wAt h (fun t => U' t i) (epE (X.ep l) σ))

def excSet (D : D7) : Finset ℕ := D.host.small ∪ {D.host.q, D.host.d, D.host.pde, D.host.pde'}

def ramSet (D : D7) : Finset ℕ := D.host.small ∪ {D.host.q, D.host.d}

def InBox (D : D7) (h : ℕ) (lam : D.what₂.Tau → DomWeight D.R.nV) : Prop :=
  ∀ τ i, 0 ≤ Uv (lam τ) i ∧ Uv (lam τ) i ≤ (h : ℤ)

def ArchimedeanSignatureMatching (D : D7) (X : Prov D) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ∉ ramSet D → ∀ (h : ℕ) (c : X.Lev l), X.hyp l c →
    ∀ (mu : D.what₂.Tau → DomWeight D.R.nV) (mt : Ideal (X.Hk l c)) [mt.IsMaximal],
    (∃ y ∈ locSet mt.primeCompl (MN X l c mu), ∀ a : X.O l, a ≠ 0 → algebraMap (X.O l) (X.Hk l c) a • y ≠ 0) →
    ∃ r ∈ crysRep X l h (fun τ => Uv (mu τ)), X.attached l h c mt r

def LogarithmicExponentBound (D : D7) : Prop :=
  ∀ l : ℕ, l.Prime → ∀ (lam : DomWeight D.R.nV) (w : ℕ), (∀ i j, Uv lam i - Uv lam j ≤ (w : ℤ)) →
    ex l lam ≤ D.R.nV.choose 2 * Nat.log l w ∧ (w < l → ex l lam = 0)

def ExponentBlockSplitting (D : D7) : Prop :=
  ∀ l : ℕ, l.Prime → ∀ (h : ℕ) (lam : DomWeight D.R.nV) (xm xp : ℤ),
    (∀ i, 0 ≤ Uv lam i ∧ Uv lam i ≤ (h : ℤ)) →
    (∀ i : Fin D.R.nV, (i : ℕ) < kCl D → xm ≤ Uv lam i ∧ Uv lam i ≤ xp) →
    ex l lam ≤ ex l (topRows lam (kCl D)) + ex l (botRows lam (kCl D)) +
      kCl D * (D.R.nV - kCl D) * Nat.log l h ∧
    ex l (topRows lam (kCl D)) ≤ (kCl D).choose 2 * Nat.log l (xp - xm).toNat ∧
    ((xp - xm).toNat < l → ex l (topRows lam (kCl D)) = 0) ∧
    (∀ w : ℤ, RowsWidth (Uv lam) (kCl D) w →
      ex l (botRows lam (kCl D)) ≤ (D.R.nV - kCl D).choose 2 * Nat.log l w.toNat ∧
        (w.toNat < l → ex l (botRows lam (kCl D)) = 0)) ∧
    (ex l (topRows lam (kCl D)) : ℝ) ≤ (kCl D : ℝ) ^ 2 * (Nat.log l ((xp - xm).toNat + kCl D) : ℝ) ∧
    ((xp - xm).toNat + kCl D < l → ex l (topRows lam (kCl D)) = 0) ∧
    (∀ w : ℤ, RowsWidth (Uv lam) (kCl D) w → w + (D.R.nV : ℤ) < (l : ℤ) →
        ex l (botRows lam (kCl D)) = 0) ∧
    (ex l (botRows lam (kCl D)) : ℝ) ≤
        ((D.R.nV : ℝ) - (kCl D : ℝ)) ^ 2 * Real.logb (l : ℝ) (2 * (h : ℝ) + (D.R.nV : ℝ))

def Conclusion1 (D : D7) (L : SizeData₂ D) (X : Prov D) : Prop :=
  (∀ l ∈ excSet D, l.Prime → ∀ (lam : D.what₂.Tau → DomWeight D.R.nV),
    (∀ (c : X.Lev l) (mt : Ideal (X.Hk l c)) [mt.IsMaximal], Incl X l c lam mt (JA D l lam)) ∧
    (∀ h : ℕ, InBox D h lam → (h : ℝ) ≤ 2 * L.sc.b → (D.R.nV : ℝ) ≤ L.sc.b → 3 ≤ L.sc.b →
      (JA D l lam : ℝ) * Real.log l ≤ (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * L.sc.L)) ∧
  (∀ (i : Fin 2) (h : ℕ) (lam : D.what₂.Tau → DomWeight D.R.nV),
    InBox D h lam → (h : ℝ) ≤ 2 * L.sc.b → ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g i : ℝ) →
    (D.R.nV : ℝ) ≤ L.sc.b → 3 ≤ L.sc.b →
    ∀ (c : X.Lev (D.host.g i)) (mt : Ideal (X.Hk (D.host.g i) c)) [mt.IsMaximal],
      Incl X (D.host.g i) c lam mt 0) ∧
  (∀ l : ℕ, l.Prime → l ∉ excSet D →
    ∀ (lam : D.what₂.Tau → DomWeight D.R.nV) (c : X.Lev l) (mt : Ideal (X.Hk l c)) [mt.IsMaximal],
      Incl X l c lam mt (JA D l lam)) ∧
  LogarithmicExponentBound D ∧ ExponentBlockSplitting D

def depth (D : D7) (h l : ℕ) (lam : D.what₂.Tau → DomWeight D.R.nV) (sh : D.what₂.Tau → ShapeData)
    (τ : D.what₂.Tau) : ℝ :=
  ((sh τ).q : ℝ) * (h : ℝ) +
    ((l : ℝ) * (mwF D D.R.t h l (fun τ => Uv (lam τ)) sh τ : ℝ) +
      (mw D D.R.t h l (fun τ => Uv (lam τ)) sh τ : ℝ)) * ((D.R.t : ℝ) + 2 * (kap h l : ℝ))

def cW (D : D7) (h l : ℕ) (lam : D.what₂.Tau → DomWeight D.R.nV) (sh : D.what₂.Tau → ShapeData)
    (τ : D.what₂.Tau) : ℝ :=
  (((sh τ).q : ℝ) + 2 * ((sh τ).j : ℝ)) * (((h : ℝ) + (D.R.nV : ℝ)) / ((l : ℝ) - 1) + 6) +
    (ex l (topRows (lam τ) (kCl D)) : ℝ) +
    (kCl D : ℝ) * ((((sh τ).xp - (sh τ).xm : ℤ) : ℝ) / (l : ℝ) + Il (sh τ).xm (sh τ).xp (sh τ).maxB l) +
    (if ((d0 (sh τ).xm (sh τ).maxB l : ℕ) : ℤ) < (sh τ).xm - (sh τ).maxB then
        min (min (kCl D : ℝ) (D.R.t : ℝ)) (depth D h l lam sh τ / (d0 (sh τ).xm (sh τ).maxB l : ℝ))
      else 0) +
    depth D h l lam sh τ / (l : ℝ) * (1 + max 0 (Real.log ((h : ℝ) / (l : ℝ))))

def lJ (D : D7) (L : SizeData₂ D) (h : ℕ) : ℝ :=
  (D.R.m : ℝ) * L.sc.b * L.sc.x ^ L.sc.eps /
    ((D.R.k : ℝ) * ((D.R.m : ℝ) + (D.R.t : ℝ)) * Real.log (3 * (h : ℝ)))

def S2 (D : D7) (L : SizeData₂ D) (A0 : ℝ) (h : ℕ) (eta S h0 lStar : ℝ)
    (lam : D.what₂.Tau → DomWeight D.R.nV) (sh : D.what₂.Tau → ShapeData) : Prop :=
  InBox D h lam ∧
  L.sc.b ≤ (h : ℝ) ∧ (h : ℝ) ≤ 2 * L.sc.b ∧
  (D.R.t : ℝ) ≤ eta ∧ Real.log eta ≤ L.sc.x ^ (L.sc.eps / 4) ∧
  (∃ g : ℝ, 1 ≤ g ∧ S = (D.R.k : ℝ) * g ∧ Real.log g ≤ L.sc.x ^ (L.sc.eps / 4)) ∧
  (D.R.nV : ℝ) ≤ L.sc.x ^ A0 ∧ (D.R.t : ℝ) ≤ L.sc.x ^ A0 ∧ (D.R.f : ℝ) ≤ L.sc.x ^ A0 ∧
  (∀ i : Fin 2, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g i : ℝ)) ∧
  (∀ τ, HasShape (kCl D) D.R.t D.R.m (Uv (lam τ)) (sh τ)) ∧
  (∀ τ, embG D τ ∈ D.host.thickPlaces →
    ((((sh τ).xp - (sh τ).xm : ℤ) : ℝ) ≤ S) ∧
    (∃ w : ℤ, RowsWidth (Uv (lam τ)) (kCl D) w ∧ (w : ℝ) ≤ 2 * eta) ∧
    ∀ i : Fin D.R.nV, (i : ℕ) < kCl D → ∀ x ∈ blockSet D.R.t (sh τ).maxB,
      L.sc.b - (D.R.t : ℝ) / 2 ≤ ((Uv (lam τ) i - x : ℤ) : ℝ) ∧
        ((Uv (lam τ) i - x : ℤ) : ℝ) ≤ L.sc.b + S + eta + 1 + (D.R.t : ℝ) / 2) ∧
  (∀ τ, embG D τ ∉ D.host.thickPlaces → Width (Uv (lam τ)) (L.sc.b' * L.sc.x ^ A0)) ∧
  0 < lStar ∧ 12 * L.sc.b / lStar + 2 * (D.R.t : ℝ) + 8 ≤ h0 ∧ lStar < lJ D L h ∧
  2 * eta + (D.R.t : ℝ) + 8 * L.sc.b / lStar + 7 < lStar ∧
  (∀ τ (i : Fin D.R.nV), IsLow (kCl D) D.R.t (sh τ) i → ∀ x ∈ blockSet D.R.t (sh τ).maxB,
    h0 / 2 - 1 - (D.R.t : ℝ) / 2 ≤ |((Uv (lam τ) i - x : ℤ) : ℝ)| ∧
      |((Uv (lam τ) i - x : ℤ) : ℝ)| ≤ eta + (D.R.t : ℝ) / 2) ∧
  (∀ τ, embG D τ ∉ D.host.thickPlaces → ∀ i : Fin D.R.nV, (i : ℕ) < kCl D →
    ∀ x ∈ blockSet D.R.t (sh τ).maxB, L.sc.w'' D.R.n / 2 ≤ |((Uv (lam τ) i - x : ℤ) : ℝ)|)

theorem S2.mono {L : SizeData₂ D} {A0 A0' : ℝ} (hA : A0 ≤ A0') {h : ℕ} {eta S h0 lStar : ℝ}
    {lam : D.what₂.Tau → DomWeight D.R.nV} {sh : D.what₂.Tau → ShapeData}
    (H : S2 D L A0 h eta S h0 lStar lam sh) : S2 D L A0' h eta S h0 lStar lam sh := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := H
  have hx0 : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hx : L.sc.x ^ A0 ≤ L.sc.x ^ A0' := Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le hA
  refine ⟨h1, h2, h3, h4, h5, h6, h7.trans hx, h8.trans hx, h9.trans hx, h10, h11, h12,
    fun τ hτ => ?_, h14, h15, h16, h17, h18, h19⟩
  obtain ⟨lo, hlo⟩ := h13 τ hτ
  refine ⟨lo, fun i => ⟨(hlo i).1, ?_⟩⟩
  have hp : 0 < L.sc.x ^ A0 := Real.rpow_pos_of_pos hx0 _
  have hb : 0 ≤ L.sc.b' := by
    by_contra hn
    push_neg at hn
    have := mul_neg_of_neg_of_pos hn hp
    linarith [(hlo i).1, (hlo i).2]
  have := mul_le_mul_of_nonneg_left hx hb
  linarith [(hlo i).2]

def a0Of (l : List ℝ) : ℝ := max (l.getD 0 0 + 1) 6

theorem initial_exponent_of_output {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : a0Of Fm.cOut = max (Fm.Ct + 1) 6 := rfl

end Formalism.MainNotions.JumpSetsAlt

end
