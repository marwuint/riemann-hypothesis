import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.Vert.Flag

theorem isSubbundle_ι_comp {X : Scheme.{0}} {E K : X.Modules} {i : K ⟶ E} {r : ℕ}
    (hi : IsSubbundle i) (fl : Vert.Flag K r) (j : Fin (r + 1)) : IsSubbundle (fl.ι j ≫ i) := by
  have := hi.mono
  obtain ⟨s, hs⟩ := hi.isVB_cokernel
  obtain ⟨h, -⟩ := VBExt.isVB_and_cls_det_of_shortExact X _ _ _
    (Vert.shortExact_cokernel_comp (fl.ι j) i) (fl.isVB_cokernel j) hs
  exact ⟨inferInstance, _, h⟩

end GlobalTheory.Vert.Flag
