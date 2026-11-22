import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.RiemannLatticeEigenProjections
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.EigenProjectionConjugateInner
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

section Ip

variable (R : RiemLat E g Λ)

theorem ip_add_right (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_smul_right (c : ℂ) (x y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem ip_conj (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip x y) = R.ip y x := by
  show star (y ⬝ᵥ R.Hm *ᵥ star x) = x ⬝ᵥ R.Hm *ᵥ star y
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

def ipL (x : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun := R.ip x
  map_add' := ip_add_right R x
  map_smul' c y := ip_smul_right R c x y

theorem ip_add_left (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  rw [← ip_conj R y, ip_add_right, map_add, ip_conj, ip_conj]

theorem ip_smul_left (c : ℂ) (x y : Fin g → ℂ) : R.ip (c • x) y = starRingEnd ℂ c * R.ip x y := by
  rw [← ip_conj R y, ip_smul_right, map_mul, ip_conj]

def TanSp (_ : RiemLat E g Λ) : Type := Fin g → ℂ

instance : AddCommGroup (TanSp R) := inferInstanceAs (AddCommGroup (Fin g → ℂ))

instance : Module ℂ (TanSp R) := inferInstanceAs (Module ℂ (Fin g → ℂ))

end Ip

section Eig

variable (R : RiemLat E g Λ)

theorem ip_sum_right {A : Type} (t : Finset A) (f : A → Fin g → ℂ) (x : Fin g → ℂ) :
    R.ip x (∑ i ∈ t, f i) = ∑ i ∈ t, R.ip x (f i) := map_sum (ipL R x) f t

theorem ip_sum_left {A : Type} (t : Finset A) (f : A → Fin g → ℂ) (y : Fin g → ℂ) :
    R.ip (∑ i ∈ t, f i) y = ∑ i ∈ t, R.ip (f i) y := by
  rw [← ip_conj R y, ip_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => ip_conj R y (f i)

omit [IsCMField E] in

theorem comp_ne {s s' : E →+* ℂ} (h : s ≠ s') :
    s.comp (algebraMap (𝓞 E) E) ≠ s'.comp (algebraMap (𝓞 E) E) :=
  fun e => h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e)

omit [IsCMField E] in

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def extEmb (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (emb_injective s)

omit [IsCMField E] in
theorem extEmb_apply (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : extEmb s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (emb_injective s) a

omit [IsCMField E] in
theorem extEmb_comp (s : 𝓞 E →+* ℂ) : (extEmb s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext (extEmb_apply s)

end Eig

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.Lin
