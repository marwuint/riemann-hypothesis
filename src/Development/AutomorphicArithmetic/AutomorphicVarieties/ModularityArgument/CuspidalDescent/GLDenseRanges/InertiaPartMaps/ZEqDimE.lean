import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open scoped Matrix TensorProduct

open private au_isTeich from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.Desc.V0

private theorem ePart_zero {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) :
    ePart ρ 0 0 = ⊤ := by
  simp [ePart, opE]

private theorem card_not_dvd {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (j : ℕ) : ¬ l ∣ Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j := by
  have hl : l.Prime := Fact.out
  have hw : (s.w s.v0).under (𝓞 (Lp L)) = s.v0 := by
    ext x
    exact (s.hw s.v0 (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA s.v0 x)
  have h2 : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← s.norm_v0_eq_one, normV, ← nsmul_one]
    exact card_nsmul_eq_zero'
  have h3 : ((s.p : ℕ) : 𝓞 L) ∈ (s.w s.v0).asIdeal := by
    rw [← hw] at h2
    have h4 : algebraMap (𝓞 (Lp L)) (𝓞 L) ((s.p : ℕ) : 𝓞 (Lp L)) ∈ (s.w s.v0).asIdeal := h2
    rwa [map_natCast] at h4
  have hd : Ideal.absNorm (s.w s.v0).asIdeal ∣ Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h3)
  have hn : Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) = s.p ^ Module.finrank ℤ (𝓞 L) := by
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 L)), Algebra.norm_algebraMap]
    simp [Int.natAbs_pow]
  rw [hn] at hd
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow s.p_prime).1 hd
  have hq : Nat.card 𝓀[(s.w s.v0).adicCompletion L] = s.p ^ e := (resCard_eq_normV _).trans he
  intro h
  rw [hq] at h
  exact s.p_ne ((Nat.prime_dvd_prime_iff_eq hl s.p_prime).1 (hl.dvd_of_dvd_pow (hl.dvd_of_dvd_pow h))).symm

end UpperTheory.V.Z.Desc.V0
