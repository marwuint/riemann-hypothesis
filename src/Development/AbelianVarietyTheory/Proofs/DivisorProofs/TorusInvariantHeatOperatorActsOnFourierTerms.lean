import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionPullbackThetaValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermChartFunctionsIsWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionInvariantField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudFourierTermOfIsWeight
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat

theorem heat_acts_on_terms : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D), IsBasic Y h → ∀ (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α), ∃ σ', TActs Y h k α σ σ' := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv D h hb k α σ
  obtain ⟨τ, hτ⟩ := GlobalTheory.RayEv.exists_sec_fourierTerm R Dd.toPre O oa Y k α σ
  obtain ⟨τ', hτ'⟩ := _root_.GlobalTheory.Heat.Glue.exists_acts Y.H Y.q.left Dd.toPre.P.L Dd.toPre.P.isLB dd (fun a => (hv a).1) (⇑D) h k τ
  have hE : ∀ a (β : Dd.toPre.X) (V : Y.H.left.Opens) f, IsWt Y β V f → IsWt Y β V (dd a V f) :=
    fun a => _root_.GlobalTheory.Heat.IsInv.isWt Y (v a) (dd a) (hv a)
  choose V hV using fun i => (hb i).1
  have hle : ∀ i, h.W i ≤ LB.wchart Dd.toPre.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h.j i) :=
    fun i x hx => Set.mem_iInter.2 fun _ => h.le i hx
  have hw : ∀ i, IsWt Y α (h.W i) (rsT (τ'.f fun _ => h.j i) (h.W i)) := by
    intro i
    rw [hτ' i]
    exact _root_.GlobalTheory.Heat.WtAlg.op_isWt Y dd _ h hE hb i k α _ (_root_.GlobalTheory.Heat.TermWt.isWt_term Y k α σ τ hτ _ _ (hle i))
  obtain ⟨σ', hσ'⟩ := _root_.GlobalTheory.Heat.isTerm_of_isWt Y k α τ' h.J V (fun i _ => h.j i) (by simp only [← hV]; exact h.cover)
    (fun i => by rw [← hV i]; exact hle i) (fun i => by rw [← hV i]; exact hw i)
  exact ⟨σ', τ, τ', hτ, hσ', hτ'⟩

end GlobalTheory.Heat
