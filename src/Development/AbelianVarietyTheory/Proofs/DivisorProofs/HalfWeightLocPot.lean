import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictChernPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartDirectionalDerivativeRegularCoordinate

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory GlobalTheory.ArInt GlobalTheory.Mean4O GlobalTheory.CxPts

namespace GlobalTheory.Mean4O.ReadsProj

section Local

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} (σ : k →+* ℂ)

def HalfWeight (L : HermLB p) (g : CxPts p σ → CxPts p σ → ℝ) : Prop :=
  ∀ x, ∃ i, x ∈ ptsIn p σ (L.B.U i) ∧ ∀ z, (L.φ σ).φ i z / 2 = g x z

variable {σ} {L L' : HermLB p} {g g' : CxPts p σ → CxPts p σ → ℝ}

theorem HalfWeight.congr (h : HalfWeight σ L g) (e : ∀ x z, g x z = g' x z) : HalfWeight σ L g' := by
  rwa [← show g = g' from funext₂ e]

theorem halfWeight_locPot (L : HermLB p) : HalfWeight σ L (L.φ σ).locPot.φ :=
  fun x => ⟨_, (L.φ σ).locPot.mem_U x, fun _ => rfl⟩

theorem halfWeight_triv : HalfWeight σ (HermLB.triv p) fun _ _ => 0 :=
  fun _ => ⟨PUnit.unit, mem_ptsIn_top, fun _ => zero_div _⟩

theorem HalfWeight.tens (h : HalfWeight σ L g) (h' : HalfWeight σ L' g') :
    HalfWeight σ (L.tens L') fun x z => g x z + g' x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  obtain ⟨j, hj, e'⟩ := h' x
  exact ⟨(i, j), mem_ptsIn_inf.2 ⟨hi, hj⟩, fun z => (add_div _ _ _).trans (congrArg₂ (· + ·) (e z) (e' z))⟩

theorem HalfWeight.dual (h : HalfWeight σ L g) : HalfWeight σ L.dual fun x z => -g x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  exact ⟨i, hi, fun z => (neg_div _ _).trans (congrArg (-·) (e z))⟩

theorem HalfWeight.pow (h : HalfWeight σ L g) (m : ℕ) : HalfWeight σ (L.pow m) fun x z => m * g x z := fun x => by
  obtain ⟨i, hi, e⟩ := h x
  refine ⟨fun _ => i, CxPts.mem_pow_iff.2 hi, fun z => ?_⟩
  refine (congrArg (· / 2) ((L.φ σ).zpow_φ m _ z)).trans ?_
  simp only [← e z, mul_div_assoc, Int.cast_natCast]

theorem HalfWeight.zp (h : HalfWeight σ L g) (n : ℤ) : HalfWeight σ (zp L n) fun x z => n * g x z :=
  ((h.pow n.toNat).tens (h.pow (-n).toNat).dual).congr fun x z => by
    have e : ((n.toNat : ℤ) : ℝ) - ((-n).toNat : ℤ) = n := by exact_mod_cast Int.toNat_sub_toNat_neg n
    rw [← e]
    simp only [Int.cast_natCast]
    ring

theorem halfWeight_comb {ι : Type} [Fintype ι] {L : ι → HermLB p} {g : ι → CxPts p σ → CxPts p σ → ℝ}
    (h : ∀ i, HalfWeight σ (L i) (g i)) (n : ι → ℤ) :
    HalfWeight σ (ArInt.comb L n) fun x z => ∑ i, n i * g i x z := by
  have key (l : List ι) : HalfWeight σ (l.foldr (fun i M => (zp (L i) (n i)).tens M) (HermLB.triv p))
      fun x z => (l.map fun i => n i * g i x z).sum := by
    induction l with
    | nil => exact halfWeight_triv
    | cons i l ih => exact ((h i).zp (n i)).tens ih
  exact (key _).congr fun x z => Finset.sum_map_toList _ _

end Local

open ProjSpace

variable (N : ℕ)

end GlobalTheory.Mean4O.ReadsProj
