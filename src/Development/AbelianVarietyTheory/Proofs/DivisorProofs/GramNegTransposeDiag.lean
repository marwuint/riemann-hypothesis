import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT in
open scoped ComplexOrder in

theorem isCartanInv_cart_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    IsCartanInv (gramAt D V τ) (cart M τ) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hu
  have hJ : Formalism.REAL.Jm (M.ε τ) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> simp
  have hJ' : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1; funext a; simp only [Pi.star_apply]; split_ifs <;> simp
  have hG : gramAt D V τ * cart M τ = (M.fr τ)ᴴ * M.fr τ := by
    rw [← M.fr_gram τ]; unfold cart
    calc _ = (M.fr τ)ᴴ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.Jm (M.ε τ)) * M.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one]
  have hs : cart M τ * cart M τ = 1 := by
    unfold cart
    calc _ = (M.fr τ)⁻¹ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.Jm (M.ε τ)) * M.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one, h2]
  refine ⟨hs, ?_, ?_⟩
  · have hGh : (gramAt D V τ)ᴴ = gramAt D V τ := by
      rw [← M.fr_gram τ]; simp [Matrix.conjTranspose_mul, hJ', Matrix.mul_assoc]
    have h3 : (cart M τ)ᴴ * gramAt D V τ = gramAt D V τ * cart M τ := by
      have := congrArg Matrix.conjTranspose hG
      rw [Matrix.conjTranspose_mul, hGh, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
      rw [this, hG]
    rw [h3, Matrix.mul_assoc, hs, Matrix.mul_one]
  · rw [hG]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (M.fr_unit τ))

end GlobalTheory.FrameEquiv
