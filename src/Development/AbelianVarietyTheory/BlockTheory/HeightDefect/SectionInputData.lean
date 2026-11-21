import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def valZ (h : GenFrEx Xo c) (G : WTZ E) (f : Rul Xo c) : ∀ Z : Comp Xo c, AC Z :=
  fun Z => AddMonoidAlgebra.single G (evC h Z f)

theorem valZ_wtZ (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    valZ h (wtZ a n) f = valC h a n f := rfl

def IsSecZ (G : WTZ E) (f : Rul Xo c) : Prop :=
  IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f ∧
    ∀ (p : TRing c.F) (t : Ix Dw → (p.R)ˣ) (y y' : FrPt Xo c p.R), FrBor t y y' →
      f p y' = ((∏ i, t i ^ exZ Dw G i : (p.R)ˣ) : p.R) * f p y

theorem isSecZ_wtZ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    IsSecZ (wtZ a n) f ↔ f ∈ sec Xo c a n := by
  have key : ∀ (S : Type) [CommRing S] (t : Ix Dw → Sˣ),
      ((∏ i, t i ^ exZ Dw (wtZ a n) i : Sˣ) : S) = wchar (ex Dw a n) t := by
    intro S _ t
    rw [wchar, Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases i <;> simp [exZ, wtZ, ex]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p t y y' hb => by rw [← key]; exact h2 p t y y' hb⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p t y y' hb => by rw [key]; exact h2 p t y y' hb⟩

variable (Xo c) in

structure Input : Type where

  D : ℕ
  N : ℕ
  T : ℕ
  i : ℕ
  g0 : ℕ

  cc : ℝ

  wL : WTZ E
  wF : WTZ E
  wde : WTZ E

  Mr : Set (Rul Xo c)

  w : Fin (N + 1) → Rul Xo c
  jc : Comp Xo c → Fin (N + 1)

  np : ℕ
  thp : Fin np → Rul Xo c

  n0 : ℕ
  th0 : Fin n0 → Rul Xo c

  nk : ℕ
  thk : Fin nk → Rul Xo c

  et : Rul Xo c
  ta1 : Rul Xo c
  ta2 : Rul Xo c

  nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ

  ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ

  wsize : WTZ E → ℝ
  DF : ℝ
  cNu : ℝ
  cQuot : ℝ
  cLow : ℝ
  cLow' : ℝ
  cDim : ℝ
  cGen : ℝ
  crystallineInclusion : ℝ
  cEta : ℝ
  cBase : ℝ
  cBase' : ℝ
  cRank : ℝ
  cField : ℝ
  f : ℝ
  r : ℝ

namespace Input

variable (I : Input Xo c)

def wG₁ : WTZ E := I.wL - I.wde

def wG₂ : WTZ E := (I.D + 4 : ℕ) • I.wL - I.wF

def wF₀ : WTZ E := I.wF + I.D • I.wL

def wka : WTZ E := I.wF + I.T • I.wL

def wet : WTZ E := (I.i * I.g0) • I.wde

def toData [Fintype (Comp Xo c)] (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) :
    ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z) where
  D := I.D
  N := I.N
  T := I.T
  i := I.i
  g0 := I.g0
  cc := I.cc
  wL := I.wL
  wF := I.wF
  wde := I.wde
  ord := fun Z v G x => ordC (δ Z v) v G x
  nrm := fun Z G x P => nrmC fn (yP Z) G x P
  M := @Submodule.span (𝓞 c.F) _ _ _ (_) (valZ h I.wka '' I.Mr)
  WW := @Submodule.span (𝓞 c.F) _ _ _ (_) (Set.range fun j => valZ h I.wL (I.w j))
  Thp := @Submodule.span (𝓞 c.F) _ _ _ (_) (Set.range fun k => valZ h I.wF (I.thp k))
  Th0 := @Submodule.span (𝓞 c.F) _ _ _ (_) (Set.range fun k => valZ h I.wF₀ (I.th0 k))
  Thk := @Submodule.span (𝓞 c.F) _ _ _ (_) (Set.range fun k => valZ h I.wka (I.thk k))
  w := fun j => valZ h I.wL (I.w j)
  jc := I.jc
  np := I.np
  thp := fun k => valZ h I.wF (I.thp k)
  n0 := I.n0
  th0 := fun k => valZ h I.wF₀ (I.th0 k)
  nk := I.nk
  thk := fun k => valZ h I.wka (I.thk k)
  et := valZ h I.wet I.et
  ta1 := valZ h ((2 : ℕ) • I.wG₁) I.ta1
  ta2 := valZ h I.wG₂ I.ta2
  nu := I.nu
  ip := I.ip
  wsize := I.wsize
  DF := I.DF
  PN := I.cNu
  PQ := I.cQuot
  tableDegreeThreeBase := I.cLow
  PP0' := I.cLow'
  Pd := I.cDim
  Gc := I.cGen
  PI4 := I.crystallineInclusion
  Pet := I.cEta
  tableLineDegreeFive := I.cBase
  tableLineDegreeTwo := I.cBase'
  Prw := I.cRank
  PO := I.cField
  f := I.f
  r := I.r

end Input

variable (Xo c)

variable {Xo c}

section
variable [Fintype (Comp Xo c)] (I : Input Xo c) (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))

theorem toData_ka : (I.toData h δ fn yP).ka = I.wka := rfl
theorem toData_F₀ : (I.toData h δ fn yP).F0 = I.wF₀ := rfl
theorem toData_G₂ : (I.toData h δ fn yP).G2 = I.wG₂ := rfl

end

end GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
