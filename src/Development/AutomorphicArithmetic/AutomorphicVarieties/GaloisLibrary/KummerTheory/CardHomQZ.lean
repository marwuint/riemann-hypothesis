import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem cardTors (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : n ≠ 0) :
    Nat.card {x : QZ l // (n : ℤ) • x = 0} = l ^ n.factorization l := by
  have hl : l.Prime := Fact.out
  obtain ⟨ι, hι, hr, -⟩ := zmodToQZ l (n.factorization l)
  have hcop : ¬ l ∣ n / l ^ n.factorization l := Nat.not_dvd_ordCompl hl hn
  have hu : IsUnit ((n / l ^ n.factorization l : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).2 hcop
  have key : ∀ x : QZ l, (n : ℤ) • x = 0 ↔ x ∈ Set.range ι := by
    intro x
    rw [hr, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℤ_[l]]
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n l, mul_comm, Nat.cast_mul, mul_smul]
    rw [hu.smul_eq_zero, Nat.cast_pow]
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  exact (Nat.card_range_of_injective hι).trans (Nat.card_zmod _)

