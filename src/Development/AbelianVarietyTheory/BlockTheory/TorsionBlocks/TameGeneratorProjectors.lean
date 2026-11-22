import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.CyclotomicNorms.StatementI

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting

open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

variable (D : D7)

def cE : ℕ := D.host.QS * D.host.q * D.host.d

def cEIdeal : Ideal (𝓞 D.host.K) := Ideal.span {((cE D : ℕ) : 𝓞 D.host.K)}

def Admissible (g : ℕ) : Prop :=
  g.Prime ∧ ∃ π : 𝓞 D.host.K, π - 1 ∈ cEIdeal D ∧ Algebra.norm ℤ π = (g : ℤ)

abbrev GalE : Type := G D.host.E D.nd.Om

def OnW (σ : D.what₂.FT) : Prop := ∃ j, 1 ≤ j ∧ j ≤ D.R.m ∧ D.what₂.isot j σ ≠ ⊥

def OccursOnLevelZero (σ : D.what₂.FT) : Prop := (∃ a, D.what₂.ft a = σ) ∨ ∃ a, D.what₂.ft0 a = σ

def IsBaseChange (σ : D.what₂.FT) (Sig : List (Part D.naut.CG)) : Prop :=
  (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) ∧
  rankIso D.nd D.naut Sig = D.R.r ∧
  (∀ τ, (isoInf D.nd D.naut Sig τ).Nodup ∧ ∀ z ∈ isoInf D.nd D.naut Sig τ, ∃ n : ℤ, z = (n : ℂ)) ∧
  (∀ i : D.nd.Loc, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → ∀ w, IsSplitPl D.host w →
    isoLoc D.nd D.naut Sig w = D.naut.locW i σ w) ∧
  (∀ k v, D.nd.lab k σ v =
    D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))) ∧
  D.ntypes.bc σ = Multiset.ofList (Sig.map fun p => (p.a, p.d))

def IsGaloisRepOf {a : ℕ} (π : D.naut.CG a) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : GalE D →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
  IsSSRep r ∧
  ∀ w : PlE D.host, w ∉ placesOver D.host.E l →
    (∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
      ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        D.naut.inePol (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) s) ∧
    (D.naut.mono0 (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) ↔
      (r '' (Ine (F := D.host.E) (D.nd.plOm.1 w) : Set (GalE D))).Finite) ∧
    (D.naut.unr (D.naut.locG π w) → ∀ (B : ValuationSubring D.nd.Om) (s : GalE D),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) s →
      ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)))

def Zbar (l : ℕ) [Fact l.Prime] : Subring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by show ‖(1 : Qbar l)‖ ≤ 1; simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by show ‖(0 : Qbar l)‖ ≤ 1; simp
  neg_mem' {a} ha := by show ‖-a‖ ≤ 1; rwa [norm_neg]

def IsReduction {a l : ℕ} [Fact l.Prime] (red : Zbar l →+* Formalism.CyclotomicNorms.Fbar l)
    (r : GalE D →* GL (Fin a) (Qbar l)) (ρ : GalE D →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) : Prop :=
  IsOpen (ρ.ker : Set (GalE D)) ∧ IsSSRep ρ ∧ ∀ g, ∃ p : (Zbar l)[X],
    p.map (Zbar l).subtype = ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly ∧
    p.map red = ((ρ g : GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar l)).charpoly

def ResidualTie (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop :=
  ∀ w : D.what₂.places.Pl,
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    ∃ (ι : Qbar (D.what₂.places.resChar w) ≃+* ℂ)
      (red : Zbar (D.what₂.places.resChar w) →+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar w))
      (r : GalE D →* GL (Fin D.R.r) (Qbar (D.what₂.places.resChar w))),
      (∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val w x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1) ∧
      IsGaloisRepOf D π _ ι r ∧ IsReduction D red r (D.ntypes.rbar σ w) ∧
      ∀ k, D.what₂.places.resChar w ≠ D.host.g k → ∀ (v : D.nd.PlG k) x, x ≠ 0 →
        ∀ z : Zbar (D.what₂.places.resChar w), (z : Qbar _) = ι.symm (D.ntypes.teichC k x) →
          red z = D.ntypes.iota k v w x

def toFb (k : Fin 2) (c : (ZMod (D.host.g k))ˣ) : Fb (D.host.g k) (D.host.g_prime k) :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (c : ZMod (D.host.g k))

def LabelLaws : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (L : D.naut.LP (D.naut.plGw k v)),
    (D.naut.items₂ k _ L).Monic ∧ (D.naut.items₂ k _ L).natDegree ≤ D.naut.lpDim L ∧
    (∀ s : ℝ, D.naut.items₂ k _ (D.naut.lpTw L s) = D.naut.items₂ k _ L) ∧
    (∀ χ : D.naut.LP (D.naut.plGw k v), D.naut.lpDim χ = 1 → D.naut.unr χ →
      D.naut.items₂ k _ (D.naut.lpChar L χ) = D.naut.items₂ k _ L) ∧
    ((D.naut.items₂ k _ L).natDegree = D.naut.lpDim L →
      ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
        s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) →
        D.naut.inePol L s = (X - 1) ^ D.naut.lpDim L)

def BaseChangeRows : Prop :=
  ∀ σ, OnW D σ → ∃ Sig, IsBaseChange D σ Sig ∧ ∀ π, Sig = [⟨D.R.r, π, 1⟩] → ResidualTie D σ π

def TransferRows : Prop :=
  ∀ σ, OccursOnLevelZero D σ → (∀ v, Squarefree (D.nd.lab 0 σ v)) →
    (∀ a, 0 < a → a < D.R.r → ∃ v, ¬ ∃ q, q ∣ D.nd.lab 0 σ v ∧ q.natDegree = a) →
    D.what₂.isot D.R.m σ ≠ ⊥

def GaloisReps : Prop :=
  ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∃ r, IsGaloisRepOf D π l ι r

end GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting
