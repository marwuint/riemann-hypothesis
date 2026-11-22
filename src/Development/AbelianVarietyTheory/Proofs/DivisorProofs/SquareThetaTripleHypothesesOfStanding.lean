import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTauEOverRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridSquareRankInequalities
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCharactersIsGoodGridPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNegConjMemberHermitianLatticeSpaceData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareSkewSumSpaceIsSkewHermitianSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelConjugateDoubledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareModelNegSpaceGoodSchroedingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepDualPairCharactersBetaQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepSquarePairCharactersAlphaQuotient

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FunObj

theorem squareTriple_of_standing {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (hL : L.Is μ₀) (W : G.Weil) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) : SquareTriple W t i j := by
  intro M hM
  obtain ⟨S₀, Q, hSQ, hX⟩ := _root_.GlobalTheory.FunObj.squareChars_isGood hL t i j hst
  choose τf hτf using (_root_.GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace (D := D))
  obtain ⟨mα, mβ, hα, hβ, hκ⟩ := _root_.GlobalTheory.SquareExps.exps hL t i j hst τf hτf
  obtain ⟨v₁, hv₁P, hv₁s, hv₁l, ⟨τ₁⟩⟩ := _root_.GlobalTheory.GoodPlace.exists_good_place (G := G) hL t (S₀ ∪ Q)
  have hτP : ∀ v : (S₀ ∪ Q : Finset (HeightOneSpectrum (𝓞 D.host.F))),
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) := fun v => (hSQ v v.2).2
  let B : Base D.host.F D.host.E :=
    ⟨W.ψ, fun w => ⟨_, hτf w⟩, mα, mβ, S₀ ∪ Q, fun v => (hτP v).some, v₁, τ₁⟩
  have hB : B.IsGood D.sp.cm.sig := _root_.GlobalTheory.FunObj.base_isGood_of_standing hL W t hst B rfl fun v hv => (hSQ v hv).1
  have hemb : ∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x) := fun _ _ => rfl
  obtain ⟨e⟩ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.nonempty_num (G := G) (i := i) (j := j) hL (by omega) (by omega)
  obtain ⟨ΛV, basV, hV⟩ := _root_.GlobalTheory.FunObj.isHerm_spaceW hL W i j B τf hemb
  obtain ⟨ΛV', basV', hV'⟩ := _root_.GlobalTheory.TripleSpace.negConj_isHerm hL W i j B τf hemb
  obtain ⟨ΛW, basW, hW⟩ := _root_.GlobalTheory.SkewLat.bigSpace_isSkew hL W i j e B τf hemb
  obtain ⟨co, vac, dom, hMo⟩ := GlobalTheory.T.exists_goodSchrodingerModel_conjugateDoubled hL t i j M hM B hB _ _ rfl _ _ _ _ hV hW
  obtain ⟨co', vac', dom', hMo'⟩ := GlobalTheory.T.squareModel_negSpace_goodSchroedinger hL t i j M hM B hB _ _ rfl _ _ _ _ hV' hW
  obtain ⟨om, hom⟩ := _root_.GlobalTheory.WeilTripleW.exists_isWeil hL t i j hst B hB _ _ _ _ _ _ hV hW _ hMo
  obtain ⟨om', hom'⟩ := _root_.GlobalTheory.FunObj.squareWeil₁ hL t i j hst B hB _ _ _ _ _ _ hV' hW _ hMo'
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.Div.SquareRanks.square_ranks (G := G) hL i j
  refine ⟨e, B, ⟨(D.R.m - j - 1) / 2, (D.R.m - j) / 2, _, _, _, Model.mk co vac ((M.ν (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))).map
      (conjU (spW G i j) (J := (1 : D.host.E) • (spW G i j).gram) 1 rfl)) dom,
    Model.mk co' vac' ((M.ν (.grid (i : ℕ) (j : ℕ))).map
      (conjU (spW₁ G i j) (J := (-1 : D.host.E) • (spW₁ G i j).gram) (-1) rfl)) dom'⟩,
    ⟨alpha G t i j, beta G i j, S₀, Q⟩, om, om', ?_, ?_, hv₁l⟩
  · exact ⟨rfl, rfl, rfl, rfl, fun w => ⟨τf w, fun _ => rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
  · exact ⟨hB, ⟨h1, h2, hκ, h3, h4, hV, hV', hW, hMo, hMo'⟩, hX B subset_rfl hv₁P hv₁s hα hβ, hom, hom'⟩

end GlobalTheory.FunObj

end
