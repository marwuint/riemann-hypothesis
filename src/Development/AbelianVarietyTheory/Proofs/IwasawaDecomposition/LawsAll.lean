import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyLawBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLatticeSpanAtPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesIntegralForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyFamOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexFormsFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawNormClassSumFock
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOkAlt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

set_option maxHeartbeats 1600000 in

theorem laws_all : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (Q : PerIn I) (hQ : Q.Ok) (Pl : Rows.Places K), J.Laws emb σ hc ∧ FmLaws J Q emb σ hc Pl hI hQ := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc hF hI hJ Q hQ Pl
  have hd := GlobalTheory.T.levelPrimeDiamond_representation I J emb σ hc hF hI hJ
  have hfam : ∀ i, ((I.S i).fam emb (lamT hc i)).Ok := fun i => _root_.GlobalTheory.Mem.Col2.fam_ok (I.S i) emb σ (lamT hc i) hF (hI.step i)
  have hfamP : (Q.S'.fam emb Q.sgT).Ok := _root_.GlobalTheory.Mem.Col2.fam_ok Q.S' emb σ Q.sgT hF hQ.step
  refine ⟨⟨hd.1, hd.2, GlobalTheory.T.complexForms_finiteDimensional (I.S 0) emb σ (lamT hc 0) hF (hI.step 0), GlobalTheory.T.levelPrimeDiamond_preserves_complexForms I J emb σ hc hF hI hJ⟩, ?_⟩
  exact
    { fam := hfam
      famP := hfamP
      lev := fun i => _root_.GlobalTheory.Mem.Col2.TDat.laws_of_ok (J.A i) J.T (hI.step i) (hJ.lev i)
      good := fun i => _root_.GlobalTheory.Mem.LatGood.lawGood (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      basis := fun i => _root_.GlobalTheory.Mem.Col2.lawBasis_all (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      norm := fun i => letI := I.clFin hI i; _root_.GlobalTheory.Mem.Col2.GStep.lawNorm (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      goodP := _root_.GlobalTheory.Mem.LatGood.lawGood Q.S' emb σ Q.sgT hF hQ.step _
      basisP := _root_.GlobalTheory.Mem.Col2.lawBasis_all Q.S' emb σ Q.sgT hF hQ.step _
      normP := letI := Q.clFin hQ; _root_.GlobalTheory.Mem.Col2.GStep.lawNorm Q.S' emb σ Q.sgT hF hQ.step _
      dia_lat := _root_.GlobalTheory.Mem.Col2.DiaLat.dia_lat I J emb σ hc hF hI hJ _
      B_span := fun i w P => _root_.GlobalTheory.Mem.BSpan.span_locW_BLat I J emb σ hc hF hI hJ Pl i _ w P }

end GlobalTheory.Mem.Col2
