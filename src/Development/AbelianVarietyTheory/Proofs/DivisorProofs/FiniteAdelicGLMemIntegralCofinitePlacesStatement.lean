import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicGLMemIntegralCofinitePlaces
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicGL_mem_integral_cofinite_places : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)), {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w a}.Finite := by
  exact @GlobalTheory.GLFinPlaces.gl_mem_int_cofinite
