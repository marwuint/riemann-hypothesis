import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.HeckeIntertwinersInert
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.InertLocalIndices
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSplitProdRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct

namespace GlobalTheory.HeckeRowsCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

theorem repr_map {F E A B ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (b : Module.Basis ι F E) (φ : A →ₐ[F] B) (z : A ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) i =
      φ ((Algebra.TensorProduct.basis A b).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem coord_eq_zero {F E A B ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (b : Module.Basis ι F E) (φ : A →ₐ[F] B) (z : A ⊗[F] E) (h : Algebra.TensorProduct.map φ (AlgHom.id F E) z = 0) (i : ι) :
    φ ((Algebra.TensorProduct.basis A b).repr z i) = 0 := by
  rw [← repr_map, h, map_zero, Finsupp.zero_apply]

theorem coord_eq_zero₂ {F E A B C ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [CommRing C] [Algebra F A]
    [Algebra F B] [Algebra F C] (b : Module.Basis ι F E) (φ : A →ₐ[F] B) (ψ : B →ₐ[F] C) (z : A ⊗[F] E)
    (h : Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) z) = 0) (i : ι) :
    ψ (φ ((Algebra.TensorProduct.basis A b).repr z i)) = 0 := by
  rw [← repr_map, coord_eq_zero b ψ _ h]

theorem mul_eq_of_coord {F E A ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]
    (b : Module.Basis ι F E) (ε : A) (z : A ⊗[F] E)
    (h : ∀ i, ε * (Algebra.TensorProduct.basis A b).repr z i = (Algebra.TensorProduct.basis A b).repr z i) :
    algebraMap A (A ⊗[F] E) ε * z = z := by
  rw [← Algebra.smul_def]
  refine (Algebra.TensorProduct.basis A b).ext_elem fun i => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, h]

theorem pair_mul_eq {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (a1 : evalV F v α = 1)
    (a : AF F) (e0 : fstA F a = 0) (e1 : ∀ v', v' ≠ v → evalV F v' (sndA F a) = 0) : pairA F 0 α * a = a := by
  refine Prod.ext ((zero_mul (fstA F a)).trans e0.symm) (FiniteAdeleRing.ext _ fun w => ?_)
  change evalV F w (α * sndA F a) = evalV F w (sndA F a)
  rw [map_mul]
  by_cases hw : w = v
  · subst hw
    rw [a1, one_mul]
  · rw [e1 w hw, mul_zero]

theorem map_eq_one_iff {R S : Type} [CommRing R] [CommRing S] (π : R →+* S) {n : ℕ} (m : Matrix (Fin n) (Fin n) R) :
    m.map π = 1 ↔ ∀ i j, π ((m - 1) i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Generic

variable {D : D7}

section Inert

variable {v : HeightOneSpectrum (𝓞 D.host.F)} {P : Pl D.host.E}

theorem under_eq (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) : P.under (𝓞 D.host.F) = v :=
  HeightOneSpectrum.ext (v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top
    (Ideal.map_le_iff_le_comap.1 (le_of_eq h))).symm

theorem eq_of_under (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) {Q : Pl D.host.E} (hQ : Q.under (𝓞 D.host.F) = v) : Q = P := by
  refine (GlobalTheory.IdemSupport.eq_of_le ?_).symm
  rw [← (h : _ = P.asIdeal), Ideal.map_le_iff_le_comap, ← hQ]
  exact le_rfl

theorem isPrimeIdem_of_inert (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    IsPrimeIdem P (algebraMap _ (Formalism.L2.Theta.AE D) ε) (algebraMap _ _ ε) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.IdemSupport.place_comp hΦ hε
  exact Or.inr ⟨rfl, ⟨v, ε, hε, rfl⟩, (GlobalTheory.IdemSupport.tie_iff hΦ (GlobalTheory.IdemSupport.place_idem hΦ hε) h0 P).2
    ⟨h0, h1 P (under_eq h), fun Q hQ => h2 Q fun e => hQ (eq_of_under h e)⟩⟩

end Inert

section Local

variable (V : HSp D)

theorem locAt_iff (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Bridge.Gf V) :
    IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v x ↔ IndefiniteRowSideFullHecke.InertLocalIndices.LocAt V v x := Iff.rfl

def cmp (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom

def locGrp (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (Bridge.Gf V) :=
  ⨅ (v') (_ : v' ≠ v), ((Formalism.UG.bc (cmp D v')).comp (finHom V).range.subtype).ker

theorem mem_locGrp {v : HeightOneSpectrum (𝓞 D.host.F)} {x : Bridge.Gf V} : x ∈ locGrp V v ↔ IndefiniteRowSideFullHecke.InertLocalIndices.LocAt V v x := by
  simp only [locGrp, Subgroup.mem_iInf]
  exact forall₂_congr fun v' _ => ⟨fun h => congrArg Units.val h, fun h => Units.ext h⟩

abbrev fin : GA D V →* Bridge.Gf V := (finHom V).rangeRestrict

theorem idem_mul_eq {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (z : Formalism.L2.Theta.AE D)
    (h0 : infPart D z = 0) (h1 : ∀ v', v' ≠ v → cmp D v' (finPart D z) = 0) : algebraMap _ (Formalism.L2.Theta.AE D) ε * z = z := by
  obtain ⟨α, rfl, a1, -⟩ := hε
  exact mul_eq_of_coord (Module.finBasis D.host.F D.host.E) _ z fun i => pair_mul_eq a1 _
    (coord_eq_zero _ (fstA D.host.F) z h0 i) fun v' hv => coord_eq_zero₂ _ (sndA D.host.F) (evalV D.host.F v') z (h1 v' hv) i

theorem suppF_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {g : GA D V}
    (hg : g ∈ GfC V) : SuppF V (algebraMap _ _ ε) g ↔ fin V g ∈ locGrp V v := by
  have key : ∀ v', (Units.val (finHom V g)).map (cmp D v') = (Formalism.L2.Theta.mt V g).map ((cmp D v').comp (finPart D)) :=
    fun _ => rfl
  rw [mem_locGrp]
  constructor
  · intro h v' hv
    refine (key v').trans ((map_eq_one_iff _ _).2 fun i j => ?_)
    obtain ⟨α, rfl, -, a0⟩ := hε
    have h2 : (cmp D v').comp (finPart D) (algebraMap _ (Formalism.L2.Theta.AE D) (pairA D.host.F 0 α)) = 0 := by
      change evalV D.host.F v' α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [a0 v' hv, TensorProduct.zero_tmul]
    rw [← h i j, RingHom.map_mul, h2, zero_mul]
  · intro h i j
    have h0 : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
    exact idem_mul_eq hε _ ((map_eq_one_iff _ _).1 h0 i j)
      fun v' hv => (map_eq_one_iff _ _).1 ((key v').symm.trans (h v' hv)) i j

theorem fin_lift (x : Bridge.Gf V) : ∃ g ∈ GfC V, fin V g = x := by
  obtain ⟨x, g, rfl⟩ := x
  let f : Formalism.L2.Theta.AE D := algebraMap _ _ (pairA D.host.F 0 1)
  have hp : pairA D.host.F 0 1 * pairA D.host.F 0 1 = pairA D.host.F 0 1 :=
    Prod.ext (mul_zero (0 : Ainf D.host.F)) (mul_one (1 : Af D.host.F))
  have hff : f * f = f := by rw [← RingHom.map_mul, hp]
  obtain ⟨g₁, g₂, h₁, h₂, rfl⟩ := GlobalTheory.IdemSupport.exists_split V hff (GlobalTheory.IdemSupport.cA_algebraMap _) g
  have b : finHom V g₂ = 1 := by
    refine Units.ext ((map_eq_one_iff (finPart D) _).2 fun i j => ?_)
    have h3 : finPart D (1 - f) = 0 := by
      rw [RingHom.map_sub, RingHom.map_one, sub_eq_zero]
      rfl
    refine (congrArg (finPart D) (h₂ i j)).symm.trans ?_
    rw [RingHom.map_mul, h3, zero_mul]
  refine ⟨g₁, GlobalTheory.IdemSupport.mem_GfC_of_suppF V (TensorProduct.zero_tmul _ _) h₁, Subtype.ext ?_⟩
  show finHom V g₁ = finHom V (g₁ * g₂)
  rw [map_mul, b, mul_one]

end Local

end GlobalTheory.HeckeRowsCompare

end
