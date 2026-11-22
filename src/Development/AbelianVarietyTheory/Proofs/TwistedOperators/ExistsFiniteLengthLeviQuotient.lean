import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingTopEmb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatSweepSmoothlyInduced
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankFiltrationExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmIndCoinvariants
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences Matrix Topology

namespace GlobalTheory.ThetaGLCover

section Strata

open GlobalTheory.RankStrataProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]

theorem continuous_slice {X G : Type} [TopologicalSpace X] [TopologicalSpace G] (r : X → G → X)
    (h : Continuous fun p : X × G => r p.1 p.2) (g : G) : Continuous fun x => r x g :=
  h.comp (Continuous.prodMk_left g)

def embL (e : c ⊕ d ≃ a) : Levi k (Two c d) →* parabLower k (two e) :=
  (leviEmb k (two e)).codRestrict _ fun _ => leviEmb_mem_parabLower k _ _

variable (k a b) in

def rChar : GL a k →* ℂˣ := (omChar a b 1).comp (MonoidHom.inl _ _)

variable (k b) in

def levRep (e : c ⊕ d ≃ a) (s : Set ℕ) : Representation ℂ (Levi k (Two c d)) (SB (ColZero k b e s)) :=
  twist (sbRep (fun y g => pAct e s y (embL e g))
    (fun y => Subtype.ext (by rw [map_one]; exact rAct_one s y.1))
    (fun y g h => Subtype.ext (by rw [map_mul]; exact rAct_mul s y.1 _ _))
    (fun g => ((continuous_rAct s).comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _))
    (deltaHalf k (Two c d) * (rChar k a b).comp (leviEmb k (two e)))

theorem levRep_apply (e : c ⊕ d ≃ a) (s : Set ℕ) (g : Levi k (Two c d)) (Φ : SB (ColZero k b e s))
    (y : ColZero k b e s) : (levRep k b e s g Φ).1 y =
      ((deltaHalf k (Two c d) g * rChar k a b (leviEmb k (two e) g) : ℂˣ) : ℂ) * Φ.1 (pAct e s y (embL e g)) := rfl

def colL (e : c ⊕ d ≃ a) (s : Set ℕ) (y : ColZero k b e s) (h : GL b k) : ColZero k b e s :=
  ⟨lAct s y.1 h, fun i j => by rw [lAct_val, mul_apply]; simp [y.2]⟩

omit [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] in
theorem continuous_colL (e : c ⊕ d ≃ a) (s : Set ℕ) :
    Continuous fun p : ColZero k b e s × GL b k => colL e s p.1 p.2 :=
  ((continuous_lAct s).comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

def leftRep (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) :
    Representation ℂ (GL b k) (SB (ColZero k b e s)) :=
  twist (sbRep (colL e s) (fun y => Subtype.ext (lAct_one s y.1))
    (fun y g h => Subtype.ext (lAct_mul s y.1 g h))
    (continuous_slice (colL e s) (continuous_colL e s))) ψ

omit [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] in
theorem leftRep_apply (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) (h : GL b k) (Φ : SB (ColZero k b e s))
    (y : ColZero k b e s) : (leftRep e s ψ h Φ).1 y = (ψ h : ℂ) * Φ.1 (colL e s y h) := rfl

def leftOp (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) (h : GL b k) :
    (levRep k b e s).IntertwiningMap (levRep k b e s) where
  toLinearMap := leftRep e s ψ h
  isIntertwining' g := LinearMap.ext fun Φ => Subtype.ext (funext fun y => by
    have : pAct e s (colL e s y h) (embL e g) = colL e s (pAct e s y (embL e g)) h :=
      Subtype.ext (Subtype.ext (by
        show (rAct s (lAct s y.1 h) _).1 = (lAct s (rAct s y.1 _) h).1
        rw [rAct_val, lAct_val, lAct_val, rAct_val, Matrix.mul_assoc]))
    rw [LinearMap.comp_apply, LinearMap.comp_apply, leftRep_apply, levRep_apply, levRep_apply, leftRep_apply, this,
      mul_left_comm])

end Strata

end GlobalTheory.ThetaGLCover
