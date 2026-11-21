import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentitySnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOfInvariantPullbackGenerator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.DescGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackLineBundleGeneratorAdditivityDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditivityDefectGeneratorInvariantSameImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentityFlatSurjectiveAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

namespace GlobalTheory.CharKer

theorem isAdditive_of_isEquivGen : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' N T : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → M.IsLB → IsEquivGen i q χ M e → IsAdditive M := by
  intro K _ _ A A' N T _ _ _ i q χ M e hA hA' hi hq hfin hflat hsurj hker hχ hM he
  haveI := hA
  haveI := hq
  haveI : IsCommMonObj A := IsAbelianScheme.comm
  obtain ⟨h₁, h₂, h₃⟩ := _root_.GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom _ A A' T q hflat hsurj inferInstance
  exact isAdditive_of_universal hM (_root_.GlobalTheory.CharKer.triv_of_isPullGen_of_invariant _ _ (pmap2 q T).left h₁ h₂ h₃ (addBundle M) (addGen q M e)
    (_root_.GlobalTheory.CharKer.isPullGen_addGen _ A A' T q M e he.1) (_root_.GlobalTheory.CharKer.addGen_invariant _ A A' N T i q χ M e hi hker hχ he))

end GlobalTheory.CharKer
