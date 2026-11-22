import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjSpace

namespace GlobalTheory.AmpleTwistNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem nefFib_of_cls_eq {L M : HermLB p} (h : cls L.B L.isLB = cls M.B M.isLB) (hL : ArInt.NefFib L) :
    ArInt.NefFib M := by
  intro Z i _ _ κ _ _ _ hd
  have e : cls (L.B.pull i) (pull_isLB L.isLB i) = cls (M.B.pull i) (pull_isLB M.isLB i) := by
    rw [cls_pull L.isLB i, cls_pull M.isLB i, h]
  rw [← topSelf_congr κ (pull_isLB L.isLB i) (pull_isLB M.isLB i) ((cls_eq_iff _ _).1 e)]
  exact hL Z i κ hd

end GlobalTheory.AmpleTwistNef

namespace GlobalTheory.AmpleTwistNef

end GlobalTheory.AmpleTwistNef
