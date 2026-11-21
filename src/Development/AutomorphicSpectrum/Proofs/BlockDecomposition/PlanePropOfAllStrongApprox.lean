import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjMemSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeFrameEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOfConjEq

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology Matrix GlobalTheory.CompanionTheory.StrongApproxSub
open Formalism.UG (UJ bc)
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.OfTwo

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {K : Matrix (Fin 2) (Fin 2) E} {a : E}
  {V : Matrix (Fin M) (Fin 2) E} {P : Matrix (Fin 2) (Fin M) E}

theorem sig_incl (e : E) :
    inclR (F := F) (E := E) (AF F) ((σ : E →+* E) e) = sigR (AF F) σ (inclR (F := F) (E := E) (AF F) e) := by
  simp [sigR, inclR]

theorem frameA (h : IsFrame (σ : E →+* E) J K a V P) :
    IsFrame (sigR (AF F) σ) (JR (AF F) J) (JR (AF F) K) (inclR (F := F) (E := E) (AF F) a) (V.map (inclR (F := F) (E := E) (AF F)))
      (P.map (inclR (F := F) (E := E) (AF F))) :=
  h.map (inclR (F := F) (E := E) (AF F)) sig_incl

def iota (h : IsFrame (σ : E →+* E) J K a V P) : HA (AF F) σ K →* HA (AF F) σ J :=
  uHom (frameA h)

theorem mt_iota (h : IsFrame (σ : E →+* E) J K a V P) (g : HA (AF F) σ K) :
    mt (iota h g) = emb0 (V.map (inclR (F := F) (E := E) (AF F))) (P.map (inclR (F := F) (E := E) (AF F))) (mt g) := rfl

end Adelic

end GlobalTheory.CompanionTheory.PlaneSA.OfTwo

end
