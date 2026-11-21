import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicFrameTorusElementMatrixEq

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorusCent

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem swap (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : IsWittFrame σ J Y X :=
  ⟨hW.yy, hW.xx, yx h hJ hW, fun z h1 h2 h3 => hW.aniso z h2 h1 h3⟩

end GlobalTheory.IdTorusCent

end
