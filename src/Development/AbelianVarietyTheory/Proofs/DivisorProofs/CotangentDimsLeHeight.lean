import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuotiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIdeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemFrobeniusKernelOfVerschiebungEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusDualAddFinrankKerVerschiebungStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup.CotDim

theorem quot_finrank_le {k A : Type} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    {I J : Ideal A} (hIJ : I ≤ J) : Module.finrank k (A ⧸ J) ≤ Module.finrank k (A ⧸ I) := by
  let f : (A ⧸ I) →ₗ[k] (A ⧸ J) := (Ideal.Quotient.factorₐ k hIJ).toLinearMap
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have := LinearMap.finrank_range_le f
  rwa [LinearMap.range_eq_top.2 hf, finrank_top] at this

theorem finrank_level_one {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k) :
    Module.finrank k (G.A 1) = p ^ G.height := by
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  have h := G.rank_eq 1 q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  simpa using h

end GlobalTheory.PDivGroup.CotDim

