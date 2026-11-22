import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwoClassFrameHasLevelSetting
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDataOfCongruentHeckeSystem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRangeOfIsAlgClosed

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.Published.CharAboveModel
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD

namespace GlobalTheory.ExpFrame.Tests

section Jumps

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

variable (Ω) in

theorem exists_bridge (τ : E →+* Qbar l) : ∃ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (_ : IsPlaceOver A w)
    (LL : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧
      IsInduced Bw τ (AlgHom.id ℚ_[l] ↥Bw.Kw.1) := by
  first
  | exact @_root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge
  | exact _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge
  | (apply _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> assumption)
  | (intros; apply _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge ..)

end Jumps

end GlobalTheory.ExpFrame.Tests

end
