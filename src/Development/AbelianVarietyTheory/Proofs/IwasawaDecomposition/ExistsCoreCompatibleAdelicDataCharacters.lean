import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothModelsOnThetaTargets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalBaseFramesFlagDomainModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDictionaryCoreLawsBaseFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreLawsForReplacedHeckeCharacters

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

theorem exists_tieIn_reCore : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → R.toLevCh.Is A.μ0 → ValKs R → FrameKs T.Q.c.F R.MW → ∃ dict mu chiW x₀, TieIn (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) ∧ LawsCore (reCore T dict mu chiW x₀ T.cE).toCore := by
  intro D G _ _ Pl0 T0 A T _ R hvol hJ hC ha hlev hval hfr
  obtain ⟨chiW, hchi, hchi'⟩ := _root_.GlobalTheory.ConjRefChar.exists_chiAt D G Pl0 T0 A T R hJ.pins ha hlev hval
  obtain ⟨x₀, hx, hx'⟩ := _root_.GlobalTheory.RealGeo.BaseFrame.exists_baseFrame D G Pl0 T0 A T R hJ ha hfr
  obtain ⟨mu, hJ1, hC1⟩ := _root_.GlobalTheory.RealGeo.exists_mu_reCore D T chiW hJ hC hchi'
  obtain ⟨dict, hJ2, hC2⟩ := _root_.GlobalTheory.BaseFrameChange.exists_dict_of_x0Orth D (reCore T T.dict mu chiW T.x₀ T.cE) x₀ hvol hJ1 hC1 hx'
  exact ⟨dict, mu, chiW, x₀, tieIn_top (reCore T dict mu chiW x₀ T.cE) R hJ2 ha
    (_root_.GlobalTheory.LowSmooth.lowSm_MW D G Pl0 T0 A T.Q.c.F R) hchi hx, hC2⟩

end GlobalTheory.RealGeo
