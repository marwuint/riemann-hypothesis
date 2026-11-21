import Formalism.LocalToGlobal.Columns.RecChainUnfOne
import Formalism.LocalToGlobal.Columns.DetChrOf
import Formalism.LocalToGlobal.Columns.WordFin
import Formalism.LocalToGlobal.Columns.TiedCB
import Formalism.LocalToGlobal.Columns.ColumnDeterminants.ColsTiedD
import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
import Formalism.LocalToGlobal.Columns.RecLevel
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.GlobalTheory.CloudNonneg
import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.HilbertSchmidtHalfBound
import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower
import Formalism.LogVandermondeBounds.LogVandermondeProofs.LogRatioLowerBoundOfLogVandermondeGap
import Formalism.GL3MeanSquares.UnitaryConjugateDiagonalMoments
import Formalism.LogVandermondeBounds.LogVandermondeProofs.UpperPlaceHolds
import Formalism.LogVandermondeBounds.LogVandermondeProofs.VandNSuccRight
import Formalism.LocalToGlobal.Columns.RecLevelCls
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.Col

namespace DetChrChi

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem isSDLat_globLat (hc : CMData F E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) :
    IsSDLat E n (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have hlat := Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top x
  have hU := globLat_unimodular hc n hx
  refine ⟨hlat.fg, hlat.span_eq_top, fun y => ?_⟩
  conv_lhs => rw [← hU]
  rw [mem_dual]
  refine forall₂_congr fun z _ => ?_
  rw [Submodule.mem_one, RingHom.mem_range]
  exact Iff.rfl

end Lat

end DetChrChi

end Formalism.L2.Col
