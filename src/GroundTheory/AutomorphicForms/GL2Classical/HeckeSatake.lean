import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.HeckeOperator
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Unimodular
import GroundTheory.AutomorphicForms.Satake
import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke

open NumberField IsDedekindDomain Matrix MeasureTheory CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm ValuativeRel Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm Rat.HeightOneSpectrum

variable (p : ℕ) [hp : Fact p.Prime]

def placeAt : HeightOneSpectrum (𝓞 ℚ) := (primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩

variable {p}

variable (p)

abbrev Qp : Type := (placeAt p).adicCompletion ℚ

variable {N : ℕ} [NeZero N]

open Spherical Iwasawa

variable {k : ℤ}

variable [MeasurableSpace (GL (Fin 2) (Qp p))] [BorelSpace (GL (Fin 2) (Qp p))]
  (μ : Measure (GL (Fin 2) (Qp p))) [μ.IsHaarMeasure]

end GL2Classical

end

end GroundTheory.Automorphic
