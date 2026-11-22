import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Formalism.LocalToGlobal.LatticeGeometry.ViewsC
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Geo NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.FamilyHypotheses

def SupBoundPageRows (D : D7) (large₂ : SizeData₂ D) {j : ℕ} (ka : WeightFamilies.Wt D j) : Prop :=
  (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧
  lrd D ≤ 2 * large₂.sc.L ∧
  Real.log D.host.d ≤ 2 * large₂.sc.L ∧
  Real.log (Ideal.absNorm D.host.ccK) ≤ 2 * large₂.sc.L ∧
  Real.log D.R.f ≤ 2 * large₂.sc.L ∧
  Real.log D.host.pde ≤ large₂.sc.L ∧
  Real.log D.host.pde' ≤ large₂.sc.L ∧
  Real.log (1 + DF ka) ≤ 2 * large₂.sc.L ∧
  Real.log ka.n ≤ large₂.sc.L

def OwnPr (D : D7) (p : ℕ) : Prop := p = Formalism.MainNotions.DIV.Cons.po D ∨ p = Formalism.MainNotions.DIV.Cons.po2 D

theorem ownPr_iff (D : D7) (p : ℕ) : OwnPr D p ↔ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ) := Iff.rfl

section Split

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def FourthHypothesisSizes (large₂ : SizeData₂ D) (C2 A2 CR : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) : Prop :=
  large₂.sc.b ≤ ka.size ∧ (T : ℝ) * wL.size ≤ 2 * ka.size ∧
  wF.size ≤ ((WeightFamilies.dimY D j : ℝ) + 2) * wL.size + 5 * D.R.f * (D.R.r : ℝ) ^ 2 * T ∧
  WeightFamilies.PPv D large₂ C2 A2 ^ 3 * (T : ℝ) ^ 2 ≤ large₂.sc.b ∧
  WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ≤ large₂.sc.b ∧
  (∀ i, 2 * DF ka + 2 < D.host.g i)

def I4 (large₂ : SizeData₂ D) (X : PJ D B P j) (wL wF : WeightFamilies.Wt D j) (nW : ℕ) : Prop :=
  ∃ PLam lNc : ℝ, PLam ≤ 1009 * Zb D large₂ ∧ lNc ≤ 81 * Zb D large₂ ^ 2 ∧
  (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th ∈ B.Mlat j w1, X.NonZeroComp w1 th ∧
    ∀ σ, Real.log (B.supN j w1 σ th) ≤ 2 * PI4 D j PLam lNc * WeightFamilies.dimY D j * wL.size) ∧
  ∃ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2 ∧ ∃ th ∈ B.Mlat j w2, X.NonZeroComp w2 th ∧
    ∀ σ, Real.log (B.supN j w2 σ th) ≤ PI4 D j PLam lNc * WeightFamilies.dimY D j * wL.size

theorem fourthHypothesis_iff_sizes_and_index (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T nW : ℕ) :
    H4 large₂ X H C2 A2 CR ka wL wF T nW ↔ FourthHypothesisSizes large₂ C2 A2 CR ka wL wF T ∧ I4 large₂ X wL wF nW :=
  ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨⟨a, b, c, d, e, f⟩, g⟩, fun ⟨⟨a, b, c, d, e, f⟩, g⟩ => ⟨a, b, c, d, e, f, g⟩⟩

def HypPage (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ)
    (h0 : ℝ) : Prop :=
  ParA large₂ H.CA ∧ SetC large₂ X H.CK H.C1 H.A1 ka wL wF T nP nW h0 ∧ H3 large₂ H C2 A2 CR 0 wL T ∧
    FourthHypothesisSizes large₂ C2 A2 CR ka wL wF T ∧ (T : ℝ) ≤ large₂.sc.x ^ CT

theorem hypC_iff (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus ↔
      HypPage large₂ X H C2 A2 CR CT ka wL wF T nP nW h0 ∧ ScalB large₂ X H.C1 H.A1 S ka wL wF T ∧
        Formalism.MainNotions.Gaps.EtaleWeightGaps.WeightedPrimeSumBoundAlt large₂ X wL nus ∧ H2 X S ka wL wF ∧ I4 large₂ X wL wF nW :=
  ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨⟨a, b, f, ((fourthHypothesis_iff_sizes_and_index ..).1 g).1, h⟩, c, d, e, ((fourthHypothesis_iff_sizes_and_index ..).1 g).2⟩,
    fun ⟨⟨a, b, f, g, h⟩, c, d, e, i⟩ => ⟨a, b, c, d, e, f, (fourthHypothesis_iff_sizes_and_index ..).2 ⟨g, i⟩, h⟩⟩

def refill {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G₀ : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData X ka wL wF)
    (del : ℕ) (th' : Fin del → B.Cusp j wF) (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ)
    (th0 : Fin rz → B.Cusp j (X.wF0 wL wF)) (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin G₀.N) →₀ ℕ) →₀ B.Cusp j ka)
    (rq : ℕ) (th : Fin rq → B.Mlat j ka) (iet : ℕ) (et : B.Cusp j (Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt D j iet)) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData X ka wL wF :=
  ⟨G₀.N, G₀.w, del, th', rz, alz, th0, zc, rq, th, iet, et, G₀.mx⟩

end Split

section Views

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}

def MSt (F : ShimFam D G Lev) : Prop := WeightFamilies.adm1 (toWeightFamilies F)

variable (F : ShimFam D G Lev) (I : Type) (dat : I → Dat D Lev) (hI : ∀ i, (dat i).Indef) (iW : ℕ → I)
  (hiW : ∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j)

def AdmissibilitySecond (large₂ : SizeData₂ D) (CA C1 A1 CG AG : ℝ) : Prop := WeightAlgebra.adm2 large₂ (toWeightAlgebra F I dat hI iW hiW) CA C1 A1 CG AG

def WSt (large₂ : SizeData₂ D) (CA C1 A1 CW AW : ℝ) : Prop := WeightAlgebra.ArchimedeanSignatureMatching large₂ (toWeightAlgebra F I dat hI iW hiW) CA C1 A1 CW AW

theorem admissibleModule_iff_lattice_quotients (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq : ℝ) :
    WeightAlgebra.admitted large₂ (toWeightAlgebra F I dat hI iW hiW) K H Ch Ah Cq Aq ↔
      MSt F ∧ AdmissibilitySecond F I dat hI iW hiW large₂ H.CA H.C1 H.A1 K.CG K.AG ∧ WeightAlgebra.adm3 large₂ (toWeightAlgebra F I dat hI iW hiW) H.CA K.Cf K.Af ∧
        WSt F I dat hI iW hiW large₂ H.CA H.C1 H.A1 K.CW K.AW ∧ WeightAlgebra.adm5 large₂ (toWeightFamilies F) K.CL K.AL ∧ WeightAlgebra.adm6 (toWeightFamilies F) K.CRm ∧
        WeightAlgebra.adm7 large₂ (toWeightFamilies F) K.CRm H.CK Ch Ah Cq Aq := Iff.rfl

end Views

end Formalism.MainNotions.Gaps.FamilyHypotheses
