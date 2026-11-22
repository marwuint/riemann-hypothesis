import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerSizes
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostCompatibilityStandardKernelDataTrueColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightCompatibilityStandardKernelDataTrueColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterCompatibilityStandardKernelDataTrueColu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticCompatibilityStandardKernelDataTrueColum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientFieldIsFieldOfDefinitionChainSteps
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColRows

theorem kerTies_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → (t.cst (I.rec7 l Z).what₂.mu0).sharp = true → GlobalTheory.ColRows.KerTies t W Del h0 := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hJ hS hW hDel hEta hSharp
  obtain ⟨hAn, hMu, hM2⟩ := _root_.GlobalTheory.ColRows.analyticTie_of_stdKer I hOk hP l Z L hT Gi Gl K Y cX ex t hJ hS
  exact
    { host := _root_.GlobalTheory.ColRows.hostTie_stdKer I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS
      wts := _root_.GlobalTheory.ColRows.weightTie_of_stdKer I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW hDel hEta
      chr := _root_.GlobalTheory.ColRows.charTie_stdKer I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW
      an := hAn
      mu0 := hMu
      sharp := hSharp
      m2 := hM2
      fld := fun u => _root_.GlobalTheory.ColRows.fieldOfDefinition_of_stdKer I hOk hP l Z L hT Gi Gl K Y cX ex t W hJ hS hW u _ }

end GlobalTheory.ColRows
