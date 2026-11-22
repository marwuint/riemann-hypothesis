import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterMonodromyZeroOfUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocDZOfSplitReg

noncomputable section

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.SplitRead GlobalTheory.CuspRep in
theorem UpperTheory.One.M.goodI_of_sph {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (π : Irr k n) (h : IsSpherical π.π) : UpperTheory.One.M.GoodI π :=
  (GlobalTheory.SphSupport.toral_and_good_of_isSpherical UpperTheory.Zero.LLC.Pr.bz k (cls (⟨π.V, π.π, π.smooth, π.irr⟩ : IrrRep (GL (Fin n) k)))
    (fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep (⟨π.V, π.π, π.smooth, π.irr⟩ : IrrRep (GL (Fin n) k))).some.symm h)).2

namespace GlobalTheory.TameType

end GlobalTheory.TameType
namespace GlobalTheory.DepthZeroAssembly
end GlobalTheory.DepthZeroAssembly
