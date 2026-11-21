import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum.Model

theorem wd_zero (D : D7) (T : Tor D) {a d : ℕ} (G : VC D a d → ℂ) : Wd D T 0 G = G := by
  funext z
  simp [Wd, wdPh, ee, qH, U, Hf]

theorem pres_vac (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d : ℕ} (e0 : VC D a d → ℂ) :
    Pres D cc δ 1 e0 e0 := by
  have h0 : pt D (tor0 D cc δ) δ (0 : Matrix (Fin d) (Fin a) D.host.E) = 0 := by
    funext τ i j
    simp [pt, embV, tor0]
  refine ⟨1, fun _ => 1, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro i; rw [h0]; simp
  · intro i; simpa using isIntegral_one
  · intro ρ; simp
  · funext y; simp [h0, wd_zero]

def spherical {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (crv : Crv D cc δ)
    (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {a d : ℕ} (had : a ≤ d) (hd : Even d)
    (e0 : VC D a d → ℂ) (vac : oddE0 D cc δ t0 a d e0) (W : WeilO D cc δ a d e0)
    (n : D.what₂.Tau → ℕ) (wt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ))
    (hfix : ∀ k ∈ intG D a, W.Om k 1 e0 = e0)
    (heig : ∀ j ∈ intG D d, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 j e0 = c • e0) : Pair D cc δ t0 1 where
  crv := crv
  pt0 := pt0
  a := a
  d := d
  a_le := had
  d_even := hd
  e0 := e0
  vac := vac
  W := W
  n := n
  wt := wt
  F := e0
  pres := pres_vac D cc δ e0
  fix := hfix
  J := intG D d
  J_le := le_rfl
  idx_ne := by simp
  idx_le := by simp
  eig := heig

instance vcUnique (D : D7) : Unique (VC D 0 0) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩

instance gaSub (D : D7) : Subsingleton (GA D 0) :=
  ⟨fun x y => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩

def triv (D : D7) : HeckeU D 0 where
  f := 1
  n := 0
  unitary := by simp
  cont := ⟨1, one_pos, by simp⟩
  aut := by simp
  norm := by simp
  par := by simp
  unr := by simp

instance cls0 (D : D7) (J : Subgroup (GA D 0)) : Unique (Cls D 0 J) :=
  ⟨⟨Quotient.mk'' 1⟩, fun x => by
    induction x using Quotient.inductionOn'
    congr 1
    exact Subsingleton.elim _ _⟩

theorem vac_mem_TT {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ} {e0 : VC D a d → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) : e0 ∈ TT D (tor0 D cc δ) a d := by
  obtain ⟨-, hW, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc a d (La0 D (tor0 D cc δ) a d)
    (Or.inr ⟨_, _, RepInv.sd_std D _, RepInv.sd_std D _, rfl⟩)
  refine ⟨he.1, 1, one_pos, fun x hx => ?_⟩
  rw [one_smul, hW x hx]
  funext w
  exact he.2 x hx w

instance vcUniqueD (D : D7) (d : ℕ) : Unique (VC D 0 d) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩

end GlobalTheory.NormSum.Model
