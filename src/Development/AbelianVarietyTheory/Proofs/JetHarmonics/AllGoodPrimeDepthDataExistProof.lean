import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthDataExistsAtPointsProof
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthDataExistsAtPointsProof
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimeDepthDataExistsAtPointsProof
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PackagesExistFrobeniusComplexConjugationStatement
import Development.AutomorphicArithmetic.OrbitLabellings.ExistsPkgCsOfDegreeBoundAtInertPrimes

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem goodPrime_packages :
    (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
        (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSt Xo c := by
  intro hU E _ _ _ H Dw lv Xo c _
  exact ⟨_root_.GlobalTheory.InertPackage.pkgInert hU E H Dw lv Xo c, (GlobalTheory.T.packages_exist_frobeniusComplexConjugation hU E H Dw lv Xo c).1, _root_.GlobalTheory.SplitPackage.pkgSplit hU E H Dw lv Xo c,
    _root_.GlobalTheory.LargePkg.pkgZero hU E H Dw lv Xo c, (GlobalTheory.T.packages_exist_frobeniusComplexConjugation hU E H Dw lv Xo c).2,
    (UpperTheory.exists_pkgCs_of_degree_bound_at_inert_primes hU E H Dw lv Xo c).1, (UpperTheory.exists_pkgCs_of_degree_bound_at_inert_primes hU E H Dw lv Xo c).2⟩

end GlobalTheory
