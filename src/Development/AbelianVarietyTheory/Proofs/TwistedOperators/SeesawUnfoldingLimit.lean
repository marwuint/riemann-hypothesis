import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKerPD
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineOneParameter
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompositionLines
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingAdelicVolume
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupMaxCompactSkewHermitia
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairCompactLineAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.KerStabCpt

theorem isHecke_quot' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem resEtaPow_quot' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) (hk : k = n + m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isPair_small' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {a a' : ℕ} {G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E}
    {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W} {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') :
    GlobalTheory.ThK.IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_quot' h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_quot' h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem algD_eq_polData {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) : algD M B.ψ B.emb = GlobalTheory.ThK.PolData B M := by
  unfold algD GlobalTheory.ThK.PolData
  congr 1
  ext Φ
  constructor
  · rintro ⟨f, φ, hf, hφ, hv, rfl⟩; exact ⟨f, hf, φ, hφ, hv, rfl⟩
  · rintro ⟨f, hf, φ, hφ, hv, rfl⟩; exact ⟨f, φ, hf, hφ, hv, rfl⟩

end GlobalTheory.SquareAgree.KerStabCpt

end
