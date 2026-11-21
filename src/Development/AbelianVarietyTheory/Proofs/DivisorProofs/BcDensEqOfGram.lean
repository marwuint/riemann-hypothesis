import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ChartGlue
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open Limits (cokernel)

namespace GlobalTheory

namespace Vert.Flag

variable {X Y : Scheme.{0}} {E : X.Modules} {N : ℕ} (fl : Flag E N) (π : Y ⟶ X)

def pull : Flag ((Scheme.Modules.pullback π).obj E) N where
  F i := (Scheme.Modules.pullback π).obj (fl.F i)
  ι i := (Scheme.Modules.pullback π).map (fl.ι i)
  isSubbundle i := SubPull.isSubbundle_pullback X Y π _ _ _ i (fl.isVB i) (fl.isSubbundle i)
  isVB i := (fl.isVB i).pullback π
  step i := (Scheme.Modules.pullback π).map (fl.step i)
  step_ι i := by rw [← Functor.map_comp, fl.step_ι]
  isIso_last := inferInstance

end Vert.Flag

namespace VMetric

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
  {E : X.Modules} {r : ℕ} (fl : Vert.Flag E r) (π : Y ⟶ X) (i : Fin r)

variable {fl π i}

theorem _root_.GlobalTheory.Met.bcDens_eq_of_gram {S : ShortComplex X.Modules} {S' : ShortComplex Y.Modules}
    {r s : ℕ} {h : Met p σ S.X₂ (r + s)} {h' : Met q σ S'.X₂ (r + s)} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r)
    (h₃' : IsVB S'.X₃ s) (H : h.IsCInf) (H' : h'.IsCInf) (a : AdaptedChart S r s)
    (a' : AdaptedChart S' r s) (c : AlgChart p σ 1) (c' : AlgChart q σ 1) {y : CxPts p σ}
    {z : CxPts q σ} (hy : y ∈ c.e.source) (hz : z ∈ c'.e.source) (ha : y ∈ ptsIn p σ a.U)
    (ha' : z ∈ ptsIn q σ a'.U) (he : c'.e z = c.e y)
    (hg : ∀ᶠ v in 𝓝 (c'.e z), h'.gram a'.frame (c'.e.symm v) = h.gram a.frame (c.e.symm v)) :
    h'.bcDens hS' h₁' h₃' c' z = h.bcDens hS h₁ h₃ c y := by
  rw [Met.bcDens_eq hS' h₁' h₃' a' c' H' hz ha', Met.bcDens_eq hS h₁ h₃ a c H hy ha, Met.bcForm,
    Met.bcForm, extTrace_congr hg, he]

end VMetric

end GlobalTheory
