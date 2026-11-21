import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.RegClosure

variable {F : Type} [Field F] [NumberField F] {d β : F}

theorem qmap_re {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).re = f x.re := rfl
theorem qmap_imI {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).imI = f x.imI := rfl
theorem qmap_imJ {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).imJ = f x.imJ := rfl
theorem qmap_imK {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).imK = f x.imK := rfl

end GlobalTheory.CompanionTheory.PlaneSA.RegClosure
