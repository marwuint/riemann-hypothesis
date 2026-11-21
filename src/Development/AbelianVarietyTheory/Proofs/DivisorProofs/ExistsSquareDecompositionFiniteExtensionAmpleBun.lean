import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexSymmetricAmpleSquareDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyRingHomComplexOfFg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleBundlesDescendFgSubfield
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianAmpleSymmPreservedFieldBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionDescendsToFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionCompatibleEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPowerDecompositionFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecFinite

theorem sqDec_of_finite_extension : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), SqDec ((Over.pullback (spMap (algebraMap K K'))).obj A) (L.pull (pullback.fst A.hom (spMap (algebraMap K K')))) (M.pull (pullback.fst A.hom (spMap (algebraMap K K')))) := by
  intro K _ _ A _ hA L M hL hM aL aM sL sM
  obtain ⟨k₀, A₀, _, π, L₀, M₀, hfg, hA₀, hπ, hL₀, hM₀, aL₀, aM₀, sL₀, sM₀, eL, eM⟩ :=
    _root_.GlobalTheory.AbFGSpread.spread_to_fg_subfield K A hA L M hL hM aL aM sL sM
  obtain ⟨σ⟩ := _root_.GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_fg K k₀ hfg
  obtain ⟨hC, aLC, sLC⟩ := _root_.GlobalTheory.FieldBaseChange.abelian_ample_symm_baseChange k₀ ℂ σ A₀ hA₀ L₀ hL₀ aL₀ sL₀
  obtain ⟨-, aMC, sMC⟩ := _root_.GlobalTheory.FieldBaseChange.abelian_ample_symm_baseChange k₀ ℂ σ A₀ hA₀ M₀ hM₀ aM₀ sM₀
  have hsq := _root_.GlobalTheory.SqDecC.sqDec_complex ((Over.pullback (spMap σ)).obj A₀) hC _ _ (pull_isLB hL₀ _) (pull_isLB hM₀ _) aLC aMC sLC sMC
  obtain ⟨k₁, _, _, _, hsq₁⟩ := _root_.GlobalTheory.SqDecFinite.main k₀ ℂ σ A₀ hA₀ L₀ M₀ hL₀ hM₀ hsq
  obtain ⟨K', _, _, _, e, he⟩ := _root_.GlobalTheory.exists_finite_ext_compat_of_finite k₀ K k₁
  exact ⟨K', inferInstance, inferInstance, inferInstance,
    _root_.GlobalTheory.SqDecTransport.transport k₀ K k₁ K' (algebraMap k₀ K) (algebraMap k₀ k₁) (algebraMap K K') e he.symm A₀ A π hπ L₀ M₀ L M hL₀ hM₀ hL hM eL eM hsq₁⟩

end GlobalTheory.SqDecFinite
