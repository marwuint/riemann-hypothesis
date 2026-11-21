import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis.SimplePoleModel

open GlobalTheory.Eis

theorem resEta_one_two_mul (D : D7) (k : ℕ) : ResEta D 1 (2 * k) :=
  ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun η h x => by
    rw [pow_mul, pow_two, GlobalTheory.VolHeckeCompare.IsEta_mul_self h x, one_pow]; rfl⟩

end GlobalTheory.Eis.SimplePoleModel

end
