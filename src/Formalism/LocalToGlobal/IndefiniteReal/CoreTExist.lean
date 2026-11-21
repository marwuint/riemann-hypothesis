import Formalism.LocalToGlobal.IndefiniteReal.FWCentral
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.ProjectiveLattices.CoreAt
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.CoreT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj
  Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Chr

theorem mem_of_latHat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) {x : Fin n → E}
    (h : (fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E))) : x ∈ Λ := by
  have key : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)),
      (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (y i)) ∈
        Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have hs : (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩)
      have hv : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈
          Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ := Submodule.subset_span ⟨x, hx, rfl⟩
      convert Submodule.smul_mem _ (⟨(1 : E) ⊗ₜ[F] a, hs⟩ : Formalism.L2.Herm.intAf F E) hv using 1
      funext i
      show Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (a ⊗ₜ[F] x i) =
        ((1 : E) ⊗ₜ[F] a) * (x i ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rfl
    | zero =>
      convert Submodule.zero_mem (Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ) using 1
      funext i
      exact map_zero _
    | add y z _ _ hy hz =>
      convert add_mem hy hz using 1
      funext i
      exact map_add _ _ _
    | neg y _ hy =>
      convert neg_mem hy using 1
      funext i
      exact map_neg _ _
  have hg : x ∈ Formalism.UG.CS.globLat (F := F) 1 Λ := by
    show ((1⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
      (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈
        Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
    exact key _ h
  rwa [Formalism.UG.P.global_lattice_one_holds F E (Fin n) Λ hfin hsp] at hg

end Chr

end Formalism.IndefR.CoreT
