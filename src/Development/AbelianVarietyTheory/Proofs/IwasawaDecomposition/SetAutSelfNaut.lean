import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq

noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne

def RowWD.unram (D : D7) (m : D.what₂.FT → PlE D.host → Multiset ℂ) (h0 : ∀ σ w, (0:ℂ) ∉ m σ w)
    (hc : ∀ σ w, Multiset.card (m σ w) = D.R.r) : RowWD D where
  par σ w := WD.lpUnr _ (m σ w)
  sat := m
  dim σ w := (WD.lpUnr_spec (m σ w) (h0 σ w)).2.2.trans (hc σ w)
  tame σ _ _ := WD.tame_of_unr (WD.lpUnr_spec (m σ _) (h0 σ _)).1

end GlobalTheory.HeightCounting
end
