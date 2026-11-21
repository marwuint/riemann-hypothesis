import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalIsometryOrthonormalMatrixUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumRationalTranslatesVsClasses
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPreservedUnitaryLatticeChanges

noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem datLoc_classes : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie Xi muT hL i hi c c'
  have hi0 : i ≤ D.R.m := Nat.le_of_succ_le hi
  have hlt : i < D.R.m := hi
  have h1 : (1 : GL (Fin (D.R.N i)) D.host.E) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi0) := one_mem _
  have h1' : (1 : GL (Fin (D.R.N (i + 1))) D.host.E) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi) := one_mem _
  have hx : ((St i hi0).y c).1 = ratA D.host.F (1 : GL (Fin (D.R.N i)) D.host.E) * ((St i hi0).y c).1 * (1 : ((St i hi0).K ((St i hi0).chOf c)).lev.U).1 := by
    simp
  have hx' : ((St (i + 1) hi).y c').1 = ratA D.host.F (1 : GL (Fin (D.R.N (i + 1))) D.host.E) * ((St (i + 1) hi).y c').1 * (1 : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U).1 := by
    simp
  have hu' := _root_.GlobalTheory.TwV.ratIsometry_unitary A dtU a hP hTie (i + 1) hi 1 h1'
  have hu := _root_.GlobalTheory.TwV.ratIsometry_unitary A dtU a hP hTie i hi0 1 h1
  have hl := _root_.GlobalTheory.TwV.latK_lev_rat A dtU a hP hTie i hi0 c ((St i hi0).y c) 1 h1 1 hx
  have hl' := _root_.GlobalTheory.TwV.latK_lev_rat A dtU a hP hTie (i + 1) hi c' ((St (i + 1) hi).y c') 1 h1' 1 hx'
  have hd := _root_.GlobalTheory.TwV.adelicDatum_at_translates A dtU a hP hTie Xi muT hL i hi c c' ((St i hi0).y c) ((St (i + 1) hi).y c') 1 h1 1 h1' 1 1 hx hx' hu'
  have hloc := hL.loc i hi ((St i hi0).chOf c) ((St (i + 1) hi).chOf c') ((St i hi0).y c) ((St (i + 1) hi).y c')
  rw [hl, hl'] at hloc
  refine _root_.GlobalTheory.TwV.datLoc_of_move D t.cc (ssRec t u μ) (t.rd u μ).lev _ _ (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x)) _ _ hu hu' ?_
  have hE : Xi i hi ((St i hi0).chOf c) ((St (i + 1) hi).chOf c') ((St i hi0).y c) ((St (i + 1) hi).y c') = _ := funext fun z => by
    have := hd z
    simpa [(hL.mu_mul i hlt).1, -Matrix.toLin'_toMatrix'] using this
  rw [hE] at hloc
  exact hloc

end GlobalTheory.TwV

end
