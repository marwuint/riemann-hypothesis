import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointFinitePartEqRealOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjUniformizerIsUniformizerConjPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitIdempotentAtConjugatePrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrimeIdempotentMulEqZeroOfVanishingAtPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCompletedSelfDualLatticeIffIntegralStdFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameTransportEtaSupportedAtPlaceIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementInvLatticeClausesOfFrameConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementUniformizerRatioDeterminant
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg

theorem eta_isHecke : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (hx1 : 1 ≤ x.2) (hx2 : x.2 ≤ (Vc X.toD7 i).rank) (v : HeightOneSpectrum (𝓞 X.toD7.host.F)) (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1) (hv : Formalism.L2.Col.IsOver v Pb) (Ut : Formalism.L2.Col.MhlUnif Pb) (g : Bridge.Gf (Vc X.toD7 i)) (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * ((Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2 : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹),
    (envL X I hX U Xg tr L cV i t).isT x g := by
  intro X px I hX U Xg tr L hI hV hL cV i t A k hF x hx1 hx2 v Pb hPb hv Ut g hg
  show x.2 ≤ (Vc X.toD7 i).rank → ∃ α, IsHeckeAt (Vc X.toD7 i) (x.1.1.1 : Pl X.toD7.host.E) x.2 α ∧ (g : GL _ _) = finHom (Vc X.toD7 i) α⁻¹
  intro _
  obtain ⟨α₀, hα₀, hfin⟩ := _root_.GlobalTheory.Mem.FinPartLift.exists_gfC_finHom_eq (Vc X.toD7 i) g
  obtain ⟨e, he⟩ := _root_.GlobalTheory.SplitEtaIdem.exists_isIdemAt_conjP Pb Ut
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.Mem.UnifConj.conj_unif_isUnif Pb Ut
  have hβ := hL.is.βV i
  rw [hL.beta.1 i] at hβ
  have hdict := _root_.GlobalTheory.Mem.SDFrameStd.lamHat_iff_int (Vc X.toD7 i) (L.ΛV i) hβ
  have heps := _root_.GlobalTheory.IdemSupp.idem_mul_eq_zero v Pb e hv he
  have hC : A * k ∈ Formalism.L2.DIV.St 1 := mul_mem hF.2.1 hF.2.2.2.2.1
  have hg' : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) (finHom (Vc X.toD7 i) α₀)) = A * k * ((Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2 : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ := by
    rw [hfin]; exact hg
  have hs := _root_.GlobalTheory.Mem.R3.LiftBrg.eta_suppAt (Vc X.toD7 i) X.B.R.nV (rkEq X i) v Pb Ut x.2 e (A * k) α₀ hv he hα₀ hg'
  have hl := _root_.GlobalTheory.Mem.R3.LiftBrg.EtaInvLat.eta_inv_lat (Vc X.toD7 i) X.B.R.nV (rkEq X i) v Pb Ut x.2 e (A * k) α₀ he heps hdict hC hα₀ hg'
  have hd := _root_.GlobalTheory.Mem.R3.LiftBrg.EtaDet.det_clause (Vc X.toD7 i) X.B.R.nV (rkEq X i) v Pb Ut x.2 e (A * k) α₀ (by rw [rkEq X i]; exact hx2) he heps hα₀ hg'
  rw [← hPb]
  refine ⟨α₀⁻¹, ⟨e, Formalism.L2.Col.cO X.toD7.host.E Ut.π, he, h1, h2, (GfC _).inv_mem hα₀, GlobalTheory.SplitPlace.suppAt_inv hs, hl.1, hl.2, hd⟩, ?_⟩
  rw [inv_inv, hfin]

end GlobalTheory.Mem.R3.LiftBrg
