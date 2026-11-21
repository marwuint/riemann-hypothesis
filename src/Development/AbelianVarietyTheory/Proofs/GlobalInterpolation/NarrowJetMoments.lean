import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ConjReal
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StandardKernelAtTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDivsOfMem

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Proof.NarrowJetMoments

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

section Notions

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

variable {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

theorem suppBar_eq (d : Deco E a ST SG) (d' : Deco E b ST SG') : JetSumTable.suppBar d d' = StandardKernelAtTorus.suppPts d d' := rfl

theorem stdAtT_iff {n : ℕ} (d : Deco E n ST SG) : JetSumTable.StdAtT d ↔ StandardKernelAtTorus.StdAtT d := Iff.rfl

end Notions

section Datum

variable {X : Fields} {a b : ℕ} {SB Sall : Finset (HeightOneSpectrum (𝓞 X.E))} {T cA cB' : ℕ}
  {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} {w : HeightOneSpectrum (𝓞 X.K)}

variable (A : Amb X)

theorem jetSum_eq (cB : ℕ) (Ξ : HomE X.E a b → X.K) :
    JetSumTable.jetSum A Sall cA cB N N' Ξ = StandardKernelAtTorus.kerTable A Sall cA cB N N' Ξ := rfl

theorem ratIdx_eq (cB : ℕ) (Ξ : HomE X.E a b → X.K) :
    JetSumTable.RatIdx A Sall cA cB N N' Ξ = {m | StandardKernelAtTorus.RatAt A Sall cA cB N N' Ξ m} := rfl

end Datum

section Bad

variable {E : Type} [Field E] [NumberField E]

theorem notMem_of_coprime {m n : ℕ} (h : Nat.Coprime m n) (P : HeightOneSpectrum (𝓞 E)) (hn : (n : 𝓞 E) ∈ P.asIdeal) :
    (m : 𝓞 E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨x, y, e⟩ := Nat.isCoprime_iff_coprime.2 h
  have e' : (x : 𝓞 E) * (m : 𝓞 E) + (y : 𝓞 E) * (n : 𝓞 E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) e
  refine (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top ?_
  rw [← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hn)

variable {X : Fields}

theorem conjP_ne_self_of_split (hX : X.Ok) {v : HeightOneSpectrum (𝓞 X.F)} (hs : SplitAt X.E v) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P.asIdeal.under (𝓞 X.F) = v.asIdeal) : conjPrime₂ P ≠ P := by
  intro hc
  have hne : GlobalTheory.MuConj.starAlg hX.star_F ≠ 1 := by
    intro h
    obtain ⟨τ⟩ : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.f_pos
    refine hX.emb_ne τ τ (RingHom.ext fun x => ?_)
    have : star x = x := congrArg (fun σ : X.E ≃ₐ[X.F] X.E => σ x) h
    show X.emb τ x = X.emb τ (star x)
    rw [this]
  have key : ∀ Q : HeightOneSpectrum (𝓞 X.E), Ideal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) v.asIdeal ≤ Q.asIdeal → Q = P := by
    intro Q hQ
    have hu : Q.under (𝓞 X.F) = P.under (𝓞 X.F) := by
      refine HeightOneSpectrum.ext ?_
      show Q.asIdeal.under (𝓞 X.F) = P.asIdeal.under (𝓞 X.F)
      rw [hP]
      exact (v.isMaximal.eq_of_le (Q.under (𝓞 X.F)).isPrime.ne_top (Ideal.map_le_iff_le_comap.1 hQ)).symm
    rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.MuConj.starAlg hX.star_F) hX.rankE hne P Q).1 hu with h | h
    · exact h
    · rw [GlobalTheory.Mem.Chr.conjPl_iff_mem] at h
      rw [← hc]
      ext y
      rw [mem_conjP]
      exact (h (cO X.E y) y (star_star (y : X.E)).symm).symm
  obtain ⟨Q, Q', hQ, hm⟩ := hs
  exact hQ ((key Q (hm ▸ Ideal.mul_le_left)).trans (key Q' (hm ▸ Ideal.mul_le_right)).symm)

variable {Pr : Primes X}

variable {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem good_of_mem_QE {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K)) :
    ∃ v, GoodPl X.E S v ∧ sel v = P := by
  classical
  unfold QE at h
  split_ifs at h with h2
  · obtain ⟨v, hv, e⟩ := Finset.mem_image.1 h
    have hv1 : v ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv
    refine ⟨v, ?_, e⟩
    by_contra hn
    have h4 := (Subgroup.mem_inf.1 mu.2).2
    exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v) hn)
  · simp at h

theorem notMem_of_mem_QE (hsel : IsSel X sel) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K))
    {l : ℕ} (hl : l.Prime) (hS : l ∈ S) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨v, hgood, e⟩ := good_of_mem_QE h
  have h5 : (l : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v, e, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hm
  apply hgood.2.2
  have h6 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ l := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h5
  haveI := v.isPrime
  rcases (Nat.dvd_prime hl).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · change ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
    rw [h7]
    exact hS

theorem mem_vGs_iff {P : HeightOneSpectrum (𝓞 X.E)} : P ∈ Pr.vGs ↔ ∃ i, P ∈ Pr.vG i := by
  classical
  unfold Primes.vGs
  rw [Finset.mem_union, Fin.exists_fin_two]

theorem g_mem (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) : (Pr.g i : 𝓞 X.E) ∈ P.asIdeal := by
  rw [← hPr.piG_norm i]
  exact Ideal.mul_mem_left _ _ (decoFin_mem_of_mem_divs h)

theorem notMem_rowSG (hPr : Pr.Ok) (hsel : IsSel X sel) {l : ℕ} (hl : l.Prime) (hS : l ∈ S) (hg : ∀ i, l ≠ Pr.g i)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  rcases Finset.mem_union.1 hP with h | h
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
    exact notMem_of_coprime ((Nat.coprime_primes hl (hPr.g_prime i)).2 (hg i)) P (g_mem hPr hi)
  · exact notMem_of_mem_QE hsel h hl hS

theorem natCast_mem_conjP {P : HeightOneSpectrum (𝓞 X.E)} {n : ℕ} :
    (n : 𝓞 X.E) ∈ (conjPrime₂ P).asIdeal ↔ (n : 𝓞 X.E) ∈ P.asIdeal := by
  rw [mem_conjP, map_natCast]

theorem conjP_notMem_rowSG (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : conjPrime₂ P ∉ rowSG Pr sel mu := by
  classical
  intro hP'
  rcases Finset.mem_union.1 hP with h | h <;> rcases Finset.mem_union.1 hP' with h' | h'
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
    obtain ⟨j, hj⟩ := mem_vGs_iff.1 h'
    by_cases hij : i = j
    · subst hij
      have h1 : X.conjO (Pr.piG i) ∈ P.asIdeal := decoFin_mem_of_mem_divs hi
      have h2 : cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal :=
        (decoFin_mem_of_mem_divs hj : X.conjO (Pr.piG i) ∈ (conjPrime₂ P).asIdeal)
      rw [cO_cO] at h2
      obtain ⟨x, y, e⟩ := hPr.piG_cop i
      refine (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top ?_
      rw [← e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h1)
    · have hne : Pr.g i ≠ Pr.g j := by
        have := hPr.g_ne
        fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
      exact notMem_of_coprime ((Nat.coprime_primes (hPr.g_prime i) (hPr.g_prime j)).2 hne) P
        (natCast_mem_conjP.1 (g_mem hPr hj)) (g_mem hPr hi)
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
    exact notMem_of_mem_QE hsel h' (hPr.g_prime i) (hS i) (natCast_mem_conjP.2 (g_mem hPr hi))
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h'
    exact notMem_of_mem_QE hsel h (hPr.g_prime i) (hS i) (natCast_mem_conjP.1 (g_mem hPr hi))
  · obtain ⟨v, hv, e⟩ := good_of_mem_QE h
    obtain ⟨v', -, e'⟩ := good_of_mem_QE h'
    have hvv : v' = v := by
      ext y
      rw [← hsel v, ← hsel v', e, e', Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP]
      have : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) y) = algebraMap (𝓞 X.F) (𝓞 X.E) y :=
        RingOfIntegers.ext (hX.star_F (y : X.F))
      rw [this]
    subst hvv
    exact conjP_ne_self_of_split hX hv.1 (e ▸ hsel v') (e'.symm.trans e)

end Bad

theorem mem_Sall {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ Sall sel mu u ↔ P ∈ Pr.vT u ∨ P ∈ rowSG Pr sel mu := by
  classical
  unfold Sall
  rw [Finset.mem_union]

end GlobalTheory.Proof.NarrowJetMoments
