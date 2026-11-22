import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorPreDataRigidificationInvPsiZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiIsEven
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataTauBimultiplicative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TensExist

theorem exists_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ D' : DegData R (maximalIdeal R), Nonempty (Tens D.toPre D'.toPre W) := by
  intro R _ _ _ hA D r W hpos hdet
  obtain ⟨D', T, hrig⟩ := _root_.GlobalTheory.Mum.TensData.main R hA D W hpos hdet
  obtain ⟨hp, ht⟩ := _root_.GlobalTheory.Mum.TensPos.psi_pos_tendsto R hA D D' W hpos T
  exact ⟨⟨D', _root_.GlobalTheory.TensEven.main R hA D D' W T, _root_.GlobalTheory.TensBimult.main R hA D D' W T hrig, hp, ht⟩, ⟨T⟩⟩

end GlobalTheory.Mum.TensExist
