import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotMemUnderLevelPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalGroupElementEqLevelComponentBadPrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEqStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfOfIsIdemSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.MovedJoin
open GlobalTheory.AdForm

open Formalism.L2.Col in

theorem adAt_kb_eq_frsF {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) (hA : A.Is) (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs)
    (i : ℕ) (hi : i ≤ B.R.m) (β : Ch₀ i) (r s : Fin (B.R.N i)) :
    adAt B.host.F P.1 (((A.kb i β : TC.GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) _) r s) =
      algebraMap B.host.E _ (frsF I.sel (I.tup a) (A.p0 i β).1.1 P (Pi.single s 1) r) := by
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have h1 := ((hA.base i hi β).1).fr ⟨P.1, hSQ⟩ r s
  rw [h1, extTo_fr, frsF_eq_ptFr]

theorem adAt_kStd_of_twist {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} (hI : I.Ok) (a : I.ι) (P : BadPr I a)
    (hP : P.1 ∉ (B.primes X).vGs) (u : B.Word) (n : ℕ) (r s : Fin n) :
    adAt B.host.F P.1 (((TC.kStd X u n : TC.GA B n) : Matrix (Fin n) (Fin n) _) r s) =
      algebraMap B.host.E _ (if r = s then 1 else 0) := by
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have hT := GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P.1 (Finset.mem_union_right _ hSQ)
  have hb := (GlobalTheory.Mem.Col2.MemChart.kStd_spec (X := X) (GlobalTheory.BasePrimes.primes_ok B X).1 u n).2.1 _ hT
  have he := congrArg (fun g => (g.1 : Matrix (Fin n) (Fin n) _) r s) hb
  simp only [Units.val_one] at he
  have h2 : Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F)) (((TC.kStd X u n : TC.GA B n) : Matrix (Fin n) (Fin n) _) r s) =
      Formalism.UG.prV (E := B.host.E) (P.1.under (𝓞 B.host.F)) ((1 : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) := by
    refine he.trans ?_
    by_cases h : r = s <;> simp [Matrix.one_apply, h]
  rw [GlobalTheory.Mem.Col2.AdT.LocSplice.adAt_eq_of_prV P.1 h2]
  by_cases h : r = s <;> simp [Matrix.one_apply, h]

theorem map_eq_one_of_pr {D : Formalism.BasicNotions.D7} {k : Type} [CommRing k] {n : ℕ} (φ : Formalism.L2.Theta.AE D →+* k)
    (M : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D))
    (h : ∀ c d, φ (M c d) = φ (Formalism.L2.Theta.incA D (if c = d then 1 else 0))) : M.map φ = 1 := by
  ext c d
  rw [Matrix.map_apply, h, Matrix.one_apply]
  split_ifs <;> simp

theorem mul_frameγ_std {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) (e' : Y ≃ Fin N)
    (hF : F.β = (1 : Matrix (Fin N) (Fin N) k).submatrix id e') (M : Matrix (Fin N) Y k) (r : Fin N) (b : Y) :
    (M * F.γ) r (e' b) = M r b := by
  have h1 : M * F.γ * F.β = M := by rw [Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 r) b
  rw [hF, Matrix.mul_apply] at h2
  simp only [Matrix.submatrix_apply, id, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  exact h2

theorem frameβ_mul_std {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) (e' : Y ≃ Fin N)
    (hF : F.β = (1 : Matrix (Fin N) (Fin N) k).submatrix id e') (g : Matrix Y Y k) (r b : Y) :
    (F.β * g) (e' r) b = g r b := by
  rw [hF, Matrix.mul_apply]
  simp only [Matrix.submatrix_apply, id, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem map_eq_sum_frame {E k : Type} [Field E] [CommRing k] {n : ℕ} (φ : E →+* k) (f : (Fin n → E) ≃ₗ[E] (Fin n → E)) (y : Fin n → E)
    (x : Fin n) : φ (y x) = ∑ c, φ (f (Pi.single c 1) x) * φ (f.symm y c) := by
  conv_lhs => rw [← f.apply_symm_apply y, pi_eq_sum_univ' (f.symm y), map_sum]
  rw [Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_comm]

end GlobalTheory.Fam.MovedJoin

namespace GlobalTheory.Fam
end GlobalTheory.Fam
