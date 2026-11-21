import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Formalism.SatakeDualWeyl.DefsCS
import Formalism.HermitianLattices.StatementMaj

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.L2.Geo.Def

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev SW : HSpace D.host.E := D.sp.W D.R.m

abbrev nW : ℕ := (SW D).rank

def Lam0 : Submodule (𝓞 D.host.E) (Fin (nW D) → D.host.E) :=
  Formalism.L2.Herm.crdLat (SW D) (SW D).L0

def inLoc (v : HeightOneSpectrum (𝓞 D.host.F))
    (x : GL (Fin (nW D)) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)) : Prop :=
  x ∈ levelVL D.sp.cm.sig (SW D).gram v (Lam0 D) ∧
    ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      Formalism.L2.Herm.InPrinc D.sp.cm (SW D) v (D.host.g i) (Lam0 D) x

abbrev GAf : Subgroup (GL (Fin (nW D)) (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)) :=
  Formalism.L2.Herm.UAf D.sp.cm (SW D)

def Kg : Subgroup (GL (Fin (nW D)) (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)) :=
  Subgroup.closure {x | x ∈ GAf D ∧ ∀ v, inLoc D v (bc (prV (E := D.host.E) v) x)}

def KgU : Subgroup (GAf D) := (Kg D).subgroupOf (GAf D)

abbrev GamF : Subgroup (GAf D) := Formalism.L2.Herm.UFin D.sp.cm (SW D)

abbrev XDef : Type := ClassSet (GamF D) (KgU D)

section Frames

variable {K : Type} [Field K] [NumberField K] [StarRing K]

open Classical in

def frameOf {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  if h : ∃ Y : Matrix ι ι ℂ, IsUnit Y.det ∧ (Y⁻¹).conjTranspose * Y⁻¹ = M then h.choose else 1

end Frames

end Formalism.L2.Geo.Def
