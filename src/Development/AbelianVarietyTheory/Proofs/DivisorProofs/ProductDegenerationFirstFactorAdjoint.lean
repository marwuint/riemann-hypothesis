import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomSectionOfProdTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInclusionFirstFactorOverAbelianInclusion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumCompMonHomEqPartialSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumInsertKilledCoordinateComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeBundleIsoExternalTensorFirstFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSumDegenerationDataFstCubeIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd

theorem adj_inl : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ := by
  intro R _ _ I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂
  obtain ⟨wM, hwM, hrig, hpsi⟩ := hS.w
  have hi₁ : IsMonHom i₁ := _root_.GlobalTheory.isMonHom_section_of_prod_trivial _ _ _ _ p₁ p₂ i₁ hS.hom₁ hS.hom₂ hS.lim e₁ e₂
  have m₁ := _root_.GlobalTheory.MumProd.PsumMap.psum_comp_hom _ _ _ _ 2 p₁ ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A]
    ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] hS.hom₁ (fun i => by
      fin_cases i
      · simp [e₁]
      · simp)
  have m₂ := _root_.GlobalTheory.MumProd.PsumCancel.psum_insert_zero_comp _ _ _ _ p₂ ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] hS.hom₂
    (by simp [e₂])
  obtain ⟨w, hw, hval⟩ := GlobalTheory.T.exists_cubeBundle_iso_externalTensor_first_factor _ _ _ _ _ D.toPre.P.L D₁.toPre.P.L D₂.toPre.P.L D.toPre.P.isLB D₁.toPre.P.isLB
    D₂.toPre.P.isLB p₁ p₂ wM hwM _ _ m₁ m₂
  exact ⟨hi₁, hS.hom₁, fun y => _root_.GlobalTheory.MumProd.c_inc_fst _ _ _ _ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ y, fun z => (hS.c_pr₁ z).symm, w, hw,
    GlobalTheory.T.periods_sumDegenerationData_fst_cube_iso R I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ wM hwM hrig hpsi w hval⟩

end GlobalTheory.MumProd
