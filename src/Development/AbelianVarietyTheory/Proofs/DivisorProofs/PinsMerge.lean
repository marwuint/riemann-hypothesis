import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffRoots
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CXiValIff
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Merge

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}

def comap {Tp Tp' : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (f : Tp' → Tp) : OMDat C R i Tp' (fun t => tup (f t)) where
  c' := O.c'
  hle := O.hle
  jL := O.jL
  hV := O.hV
  c0' := O.c0'
  lev := O.lev
  dδ := fun t => O.dδ (f t)
  Cl' := fun t => O.Cl' (f t)
  fCl := fun t => O.fCl (f t)
  bad := fun t => O.bad (f t)
  Lh := fun t => O.Lh (f t)
  La := fun t => O.La (f t)
  Nc := fun t => O.Nc (f t)
  gam := fun t => O.gam (f t)
  vol := fun t => O.vol (f t)
  ep := fun t => O.ep (f t)
  B := fun t => O.B (f t)
  epF := fun t => O.epF (f t)
  io := O.io
  hw := O.hw
  φ := fun t => O.φ (f t)
  w := fun t => O.w (f t)
  U₂ := fun t => O.U₂ (f t)
  dict₂ := fun t => O.dict₂ (f t)
  xi := fun t => O.xi (f t)
  thAd := fun t => O.thAd (f t)
  Plc := fun t => O.Plc (f t)

theorem pins_comap {Tp Tp' : Type} {tup : Tp → T0} {O : OMDat C R i Tp tup} (f : Tp' → Tp) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ ι x₀} (h : O.Pins κ v₀ ι x₀) : (comap O f).Pins κ v₀ ι x₀ :=
  ⟨h.lift, fun t => h.tuple (f t), h.act, fun t => h.bad (f t), fun t => h.reps (f t), fun t => h.ep (f t), h.io,
    fun t => h.w (f t), fun t => h.cov (f t), h.cxi.imp fun _ hc => ⟨hc.1, fun t => hc.2 (f t)⟩, fun t => h.model₂ (f t)⟩

variable {J : Type} {tup : J → T0} (src : ∀ j, OMDat C R i Unit (fun _ => tup j)) (c₃ : Coeff C.Q.l) (h₃ : C.Q.c.F ≤ c₃.F)
  (hs : ∀ j, (src j).c'.F ≤ c₃.F) (jL₃ : D.what₂.LL →+* c₃.F) (hV₃ : C.V ((i : ℕ) + 1) (sOv C c₃ h₃) = Wc D i)
  (c0₃ : VsV D i c₃.F →ₛₗ[inC c₃] (R.cV i).W)
  (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
  (io₃ : VsV D i c₃.F →ₗ[c₃.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c₃.F) (hw₃ : VsV D i c₃.F)
  (u : J → c₃.F) (h : ∀ j, (src j).Cl' () → GA D (Vc D i)) (v₀ : (R.MW i (sg0 D A)).Vec)

def merge : OMDat C R i J tup where
  c' := c₃
  hle := h₃
  jL := jL₃
  hV := hV₃
  c0' := c0₃
  lev := lev
  dδ := fun j => covBC (hs j) ((src j).dδ ()) (u j)
  Cl' := fun j => (src j).Cl' ()
  fCl := fun j => (src j).fCl ()
  bad := fun j => (src j).bad ()
  Lh := fun j => (src j).Lh ()
  La := fun j => (src j).La ()
  Nc := fun j => (src j).Nc ()
  gam := fun j => (src j).gam ()
  vol := fun j => incF _ c₃ (hs j) ((src j).vol ())
  ep := fun j k => incF _ c₃ (hs j) ((src j).ep () k)
  B := fun j I => incF _ c₃ (hs j) ((src j).B () I)
  epF := fun j L => incF _ c₃ (hs j) ((src j).epF () L)
  io := io₃
  hw := hw₃
  φ := fun j x => incF _ c₃ (hs j) ((src j).φ () x)
  w := fun j k q => incF _ c₃ (hs j) ((src j).w () k q)
  U₂ := fun j => covUnf (hs j) ((src j).dδ ()) (u j) ((src j).U₂ ())
  dict₂ := fun j => (src j).dict₂ ()
  xi := fun j => (src j).xi ()
  thAd := fun j => thAdOf R i (tup j) (h j) c0₃ v₀
  Plc := fun j x => ∃ x₀, Place R i (tup j) (h j) c0₃ (jVx R i (tup j) x₀) x

theorem repsR_map {K K' : Type} [Field K] [Field K'] (j : K →+* K') {t : T0} {Cl : Type} {h : Cl → GA D (Vc D i)} {bad J' Lh gam}
    {vol : K} (hr : RepsR R i t h bad J' Lh gam vol) : RepsR R i t h bad J' Lh gam (j vol) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  exact ⟨h1, h2, h3, h4, by rw [h5, map_inv₀, map_natCast], h6⟩

end Merge

end GlobalTheory.OneMapAll
