import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockIsTheRun
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfIsCompAlongSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfIsCompAlongSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpehPartIsRun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpehInfMapSubEqSumTwists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeLinearFactorsRegroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModel

open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalAut

noncomputable def shiftF (n d k : ℕ) : ℂ := ((n : ℂ) - 1) / 2 + (((d : ℂ) - 1) / 2 - (k : ℂ))

theorem cast_floor_re {u : ℂ} {j : ℤ} (h : u = j) : ((⌊u.re⌋ : ℤ) : ℂ) = u := by
  rw [h]; simp

theorem mem_spehInf {d : ℕ} {M : Multiset ℂ} {z : ℂ} (hz : z ∈ M) {k : ℕ} (hk : k < d) :
    z + (((d : ℂ) - 1) / 2 - (k : ℂ)) ∈ spehInf d M := by
  unfold spehInf
  refine Multiset.mem_of_le (List.le_sum_of_mem (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)) ?_
  exact Multiset.mem_map.2 ⟨z, hz, rfl⟩

theorem int_of_mem_infOfWeight {n : ℕ} {lam : DomWeight n} {x : ℂ} (hx : x ∈ infOfWeight lam) :
    ∃ j : ℤ, ((n : ℂ) - 1) / 2 - x = j := by
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
  exact ⟨(k : ℤ) - lam.w k, by push_cast; ring⟩

theorem le_sum_spehInf {c : ℕ} (d : Fin c → ℕ) (M : Fin c → Multiset ℂ) (i : Fin c) :
    spehInf (d i) (M i) ≤ ∑ j, spehInf (d j) (M j) :=
  Finset.single_le_sum (f := fun j => spehInf (d j) (M j)) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)

theorem charpoly_eq_of_one {K : Type} [CommRing K] {N : ℕ} (hN : N = 1) (M : Matrix (Fin N) (Fin N) K) :
    M.charpoly = Polynomial.X - Polynomial.C M.det := by
  subst hN
  rw [Matrix.det_fin_one]
  ext k
  simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]

theorem lift_eq (T : Multiset ℂˣ) :
    (T.map (fun z : ℂ => z) : Multiset ℂ) = T.map (fun z : ℂˣ => (z : ℂ)) := by
  simp only [Multiset.map_id']
  induction T using Multiset.induction_on with
  | empty => rfl
  | cons x s ih => simp_all

end GlobalTheory.GalAut

namespace GlobalTheory.GalAut

theorem map_cast_sum {ι' : Type} [Fintype ι'] (f : ι' → Multiset ℤ) :
    (∑ j, f j).map (fun k : ℤ => (k : ℂ)) = ∑ j, (f j).map (fun k : ℤ => (k : ℂ)) :=
  map_sum (Multiset.mapAddMonoidHom fun k : ℤ => (k : ℂ)) f Finset.univ

theorem map_sub_sum {ι' : Type} [Fintype ι'] (f : ι' → Multiset ℂ) (e : ℂ) :
    (∑ j, f j).map (fun z => e - z) = ∑ j, (f j).map (fun z => e - z) :=
  map_sum (Multiset.mapAddMonoidHom fun z : ℂ => e - z) f Finset.univ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n c : ℕ} {π : Submodule ℂ (UA E n → ℂ)} {a d : Fin c → ℕ}
  {h : ∑ i, d i * a i = n} {P : ∀ i, CuspSub E (a i)} {ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i)}
  {m : Fin c → (E →+* ℂ) → Multiset ℂ}

theorem int_of_parts (hP : GlobalTheory.BcSpeh.Parts π a d h P ρ m) {τ : E →+* ℂ} {lam : DomWeight n}
    (hl : HasWeightAt π τ lam) (i : Fin c) {z : ℂ} (hz : z ∈ m i τ) {k : ℕ} (hk : k < d i) :
    ∃ j : ℤ, ((n : ℂ) - 1) / 2 - (z + (((d i : ℂ) - 1) / 2 - (k : ℂ))) = j := by
  apply int_of_mem_infOfWeight (lam := lam)
  rw [← hP.weight τ lam hl]
  exact Multiset.mem_of_le (le_sum_spehInf d (fun j => m j τ) i) (mem_spehInf hz hk)

theorem nodup_of_parts (hP : GlobalTheory.BcSpeh.Parts π a d h P ρ m) {τ : E →+* ℂ} {lam : DomWeight n}
    (hl : HasWeightAt π τ lam) (i : Fin c) : (m i τ).Nodup := by
  have h1 : (infOfWeight lam).Nodup := nodup_infOfWeight lam
  rw [← hP.weight τ lam hl] at h1
  have h2 := Multiset.nodup_of_le (le_sum_spehInf d (fun j => m j τ) i) h1
  have h3 : (m i τ).map (· + (((d i : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤ spehInf (d i) (m i τ) := by
    unfold spehInf
    exact List.le_sum_of_mem (List.mem_map.2 ⟨0, List.mem_range.2 (hP.pos i).2, rfl⟩)
  exact (Multiset.nodup_of_le h3 h2).of_map _

theorem int_shift (hP : GlobalTheory.BcSpeh.Parts π a d h P ρ m) {τ : E →+* ℂ} {lam : DomWeight n}
    (hl : HasWeightAt π τ lam) (i : Fin c) (k : Fin (d i)) {z : ℂ} (hz : z ∈ m i τ) :
    ∃ j : ℤ, shiftF n (d i) k - z = j := by
  obtain ⟨j, hj⟩ := int_of_parts hP hl i hz (k := d i - 1 - k) (by omega)
  refine ⟨j, ?_⟩
  rw [← hj, shiftF]
  have : ((d i - 1 - (k : ℕ) : ℕ) : ℂ) = (d i : ℂ) - 1 - (k : ℂ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by have := (hP.pos i).2; omega)]; simp
  rw [this]; ring

end GlobalTheory.GalAut

namespace GlobalTheory.GalAut

theorem crystallineHodgeTate_det_rankOne {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {N : ℕ}
    (hN : N = 1) (r : G E Ω →* GL (Fin N) (Qbar l)) (J : (E →+* Qbar l) → Multiset ℤ)
    (hr : GlobalTheory.ExpFrame.CrysWith r J) : GlobalTheory.ExpFrame.CrysWith (GlobalTheory.TripleGal.rk1 (Matrix.GeneralLinearGroup.det.comp r)) J := by
  subst hN
  have : GlobalTheory.TripleGal.rk1 (Matrix.GeneralLinearGroup.det.comp r) = r := by
    ext g i j
    fin_cases i; fin_cases j
    simp [GlobalTheory.TripleGal.rk1, Matrix.det_fin_one]
  rwa [this]

end GlobalTheory.GalAut

