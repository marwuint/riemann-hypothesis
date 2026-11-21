import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEquivarianceWeilModel

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift.BaseEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem phiC_congr {D : D7} (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

theorem alg_step {l c a a' x y : ℂ} (h1 : x = l * a) (h2 : a = c * a') (h3 : y = l * a') : x = c * y := by
  rw [h1, h2, h3]; ring

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

theorem baseEmbedding_restriction_eq_coefficientInclusion (fw : FWTie T R κw v₀) : res T (sg0 D A) = T.σ₀ :=
  (congrArg (res T) (show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0)).trans (res_embLL T fw.alg_eq fw.laws.pins.2.2.1)

theorem ev_base (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hev : fw.Evaluates)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (f : Cu T κw i) (h : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).e (fw.jK i (sg0 D A) f) (v₀ i (sg0 D A)) h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κw i)) : ℂ) *
        (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) (f : T.R ((i : ℕ) + 1)) h := by
  have e : res T (sg0 D A) = (O i).s0 := (baseEmbedding_restriction_eq_coefficientInclusion T R κw v₀ fw).trans (sOv_eq T.toCore (O i).c' (O i).hle).symm
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) e).trans (O i).hV
  have h1 := hev i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV f
  have h2 := phiC_congr T e hV (O i).hV (wtA (κw i)) (f : T.R ((i : ℕ) + 1))
  have h3 := phi_cE T R O i (wtA (κw i)) (f : T.R ((i : ℕ) + 1)) h
  exact (congrFun (h1.trans h2) h).trans h3.symm

end GlobalTheory.GalLift.BaseEquiv

end
