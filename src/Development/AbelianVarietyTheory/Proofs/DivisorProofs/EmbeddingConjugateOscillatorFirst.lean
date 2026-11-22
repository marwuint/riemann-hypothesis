import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeCharMulInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomEqOnAdjoinSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolShapeOfOverK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfConjOnFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CircleEqOneIffOfConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResEtaHasInfExpOfIsEtaConj

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.Facts

theorem infPart_eq_one {D : D7} {v ε} (hε : IsPlaceIdem D v ε) {x : AE D}
    (hx : algebraMap (AF D.host.F) (AE D) ε * (x - 1) = x - 1) : infPart D x = 1 := by
  obtain ⟨α, rfl, -⟩ := hε
  have h3 := congrArg (infPart D) hx
  have h4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    have e2 : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
    have e3 := Algebra.TensorProduct.map_tmul (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 α) 1
    rw [e2, TensorProduct.zero_tmul] at e3
    exact e3
  rw [map_mul, h4, zero_mul, map_sub, map_one] at h3
  exact (sub_eq_zero.1 h3.symm)

theorem sigW_add {D : D7} (i : Fin D.R.m) :
    (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
  have := D.R.m_add_three_le_k
  have hi := i.2
  rw [rank_Wc i]
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem signs_of_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) (ρ : D.what₂.Tau) (a : Fin (Wc D i).rank) :
    (R.MW i σ).ε ρ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D ρ)).1) := by
  have hs : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have he := (R.MW i σ).enum ρ
  unfold Links.parAt at he
  rw [if_pos (((labels_overK σ).1 hσ).2 ρ)] at he
  exact (GlobalTheory.HolDict.isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs]; exact sigW_add i) he a).2

end GlobalTheory.GalOne.Facts
