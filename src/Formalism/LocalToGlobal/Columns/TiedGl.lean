import Formalism.LocalToGlobal.Columns.TiedGlPl
import Formalism.LocalToGlobal.Columns.TiedGlMat
import Formalism.LocalToGlobal.Columns.RecLevelDiv
import Formalism.LocalToGlobal.HermitianForms.FormsTied

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM InJ)

section GLc

variable {X : Fields} {Pr : Primes X} {hc : Formalism.BasicNotions.CMData X.F X.E} (hPr : Pr.Ok) (S : GSplit (Pr := Pr) hc) {m : ℕ}
  (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ)

def tieGLoc (hCh : Ch.Ok) : Formalism.L2.Forms.GLoc X.F X.E hc.sig Pr.g where
  sp := S.sp
  sp_sig := S.sp_sig
  sp_alg := S.sp_alg
  piG := Pr.piG
  piG_norm i := by
    have := congrArg (algebraMap (𝓞 X.E) X.E) (hPr.piG_norm i)
    rw [map_mul, map_natCast] at this
    exact this
  sp_pi := S.sp_pi
  psi0 i v h := glmPsi (S.eK hPr i v h) σ₀ (Ch.psi0 (gwOf hc hPr i v h))
  psi_zero_nontrivial_character i v h := by
    intro h1
    apply hCh.psi_zero_nontrivial_character (gwOf hc hPr i v h)
    ext x
    have h2 := DFunLike.congr_fun h1 (S.eK hPr i v h x)
    rw [glmPsi_apply, AddChar.one_apply] at h2
    rw [AddChar.one_apply]
    exact σ₀.injective (h2.trans (map_one σ₀).symm)
  chiB i v h s := glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) s)

end GLc

end Formalism.L2.Col
