import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.InhTate
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionPairTest

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem ext_val {T : Over (Spec (CommRingCat.of R))} {g g' : GtPt D T} (hb : g.b = g'.b)
    (hs : ∀ χ y J, Geo.Tor.Good D.P.L y J → Geo.Tor.val (g.s χ) (𝟙 _) y J = Geo.Tor.val (g'.s χ) (𝟙 _) y J) :
    g = g' := by
  obtain ⟨b, s, h, _, _⟩ := g
  obtain ⟨b', s', h', _, _⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ =>
    GlobalTheory.TorusCoord.gen_eq_of_corr D.P.isLB (h χ) (h' χ) (Geo.Tor.corr_of_val D.P.isLB (hs χ))
  rfl

theorem isPull_unique {T T' : Over (Spec (CommRingCat.of R))} {h : T'.left ⟶ T.left} {g : GtPt D T}
    {a a' : GtPt D T'} (H : GtPt.IsPull h g a) (H' : GtPt.IsPull h g a') : a = a' :=
  ext_val (Over.OverMorphism.ext (H.1.trans H'.1.symm)) fun χ _ _ hJ =>
    (Geo.Tor.val_corr hJ (H.2 χ) (𝟙 _)).trans (Geo.Tor.val_corr hJ (H'.2 χ) (𝟙 _)).symm

variable {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) (k : ℕ) (T : Over W.toScheme) [IsEmpty T.left]

instance : IsEmpty (overW W T).left := inferInstanceAs (IsEmpty T.left)

end GlobalTheory.TorsionPairTest
