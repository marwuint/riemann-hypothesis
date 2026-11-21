import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalFrameOfCoords
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrameStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedClassRepresentative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormSumRepresentativeLiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorDifferentialRepresentativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameTaylorClassEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameDerivationCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictMonoSnocPermEqSuccAboveStatement

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

def I0 (m : ℕ) : Idx m m := ⟨id, strictMono_id⟩

theorem idx_eq {m : ℕ} (I : Idx m m) : I = I0 m := by
  refine Subtype.ext ((StrictMono.range_inj I.2 strictMono_id).1 ?_)
  have h : Function.Surjective I.1 := (Finite.injective_iff_surjective).1 I.2.injective
  rw [h.range_eq, Function.surjective_id.range_eq]

instance {m : ℕ} : Unique (Idx m m) := ⟨⟨I0 m⟩, idx_eq⟩

theorem sgn_snoc {n : ℕ} (I : Idx n (n + 1)) (k : Fin (n + 1)) (h : I.1 ≠ k.succAbove) :
    sgn (I0 (n + 1)) (Fin.snoc (α := fun _ => Fin (n + 1)) I.1 k) = 0 := by
  refine Finset.sum_eq_zero fun π _ => ?_
  rw [if_neg]
  intro e
  exact h (GlobalTheory.T.strictMono_snoc_perm_eq_succAbove I.1 k π I.2 e)

theorem rep_one {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {m : ℕ} (E : Frame Φ m)
    (σ : ∀ T : C, E.D ⟶ T) (r : ℤ) (w : Idx m m → Φ.A.obj E.D) (cl : CH.H (gr Fil r) m)
    (h : CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Idx m m, E.form σ I.1 (w I) u) cl) :
    CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (E.form σ id (w (I0 m))) cl := by
  refine rep_congr h fun u => ?_
  rw [Fintype.sum_unique]
  change E.form σ (I0 m).1 (w (I0 m)) u - _ ∈ _
  rw [show (I0 m).1 = id from rfl, sub_self]
  exact Ideal.zero_mem _

end GlobalTheory.CompanionTheory.ConeLocal
