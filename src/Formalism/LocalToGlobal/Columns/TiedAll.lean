import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.TiedValAll
import Formalism.LocalToGlobal.Columns.TiedCB

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d)

set_option maxHeartbeats 1000000 in

structure FormsOwed (u : d.what₂.Word) where
  gl : GLoc d.host.F d.host.E (CF.sigD (d.colRec a)) d.host.g
  gl_K : ∀ i, (gl.piG i : d.host.E) ∈ d.host.K
  glev : ∀ i hi, GLev (classAgreement a hS hH hP u i hi).lev gl (aOf d.R i) d.R.t i (skipOf d.R i) (fcOf d.R i) (decide (i = d.R.m))
  fMe : ∀ i hi v, (classAgreement a hS hH hP u i hi).lev.fM ((atTTied a hH u).eV v).1 ((atTTied a hH u).eV v).2 ≃+
    ((d.colRec a).mem u).A.Fv v
  fv : ∀ i hi, CF.FvTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) (fMe i hi)
  upN : ∀ i hi, CF.UpNatTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) (valuationAgreementConcrete a hS hH hP u i hi)
  dnN : ∀ i hi, CF.DnNatTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) (valuationAgreementConcrete a hS hH hP u i hi)
  clsP : CF.ClsPTied (D := d.colRec a) u
  valP : CF.ValPTied (D := d.colRec a) u clsP
  normP : CF.NormPTie valP
  glevP : GLev clsP.lev gl d.R.r d.R.t d.R.m (d.R.N d.R.m) (fcOf d.R d.R.m) false
  til : CF.TilTied (D := d.colRec a) u (atTTied a hH u) clsP (levelAgreement a hS hH u d.R.m le_rfl)
  tilLat : CF.TilBaseLat til (classAgreement a hS hH hP u d.R.m le_rfl)
  tilFv : CF.TilBaseFv til (classAgreement a hS hH hP u d.R.m le_rfl) (fMe d.R.m le_rfl)
  tilAd : CF.TilAd til (classAgreement a hS hH hP u d.R.m le_rfl)
  frExt : CF.FrExt til.z0 (glev d.R.m le_rfl) glevP
  eWz : ((d.colRec a).mem u).P.Wz ≃ₗ[ℂ] (((d.colRec a).fm u).clsP → ((d.colRec a).mem u).C.Y d.R.m → ℂ)
  evz : CF.EvzTie tilAd (valuationAgreementConcrete a hS hH hP u d.R.m le_rfl) eWz
  jM : ((d.colRec a).mem u).P.Mt →ₛₗ[starRingEnd ℂ] ((d.colRec a).mem u).P.Wrow
  per : CF.PerTie (D := d.colRec a) u jM

variable {a hS hH hP}

variable (a hS hH hP)

variable {a hS hH hP}

end Formalism.L2.Col
