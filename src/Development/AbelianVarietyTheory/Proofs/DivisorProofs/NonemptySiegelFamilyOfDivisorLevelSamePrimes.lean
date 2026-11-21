import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelLevelLoweringQuotientFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelQuotientFamilyLocalPointsEqOfObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelLoweringQuotientRepresentsReduced
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegLev

theorem sFam_down : ∀ h n N : ℕ, 3 ≤ n → Odd N → n ∣ N → (∃ a, N ∣ n ^ a) → Nonempty (SFam h N (zetaAway N)) →
    Nonempty (SFam h n (zetaAway n)) := by
  intro h n N hn hN hnN hpow ⟨F⟩
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hN)
  obtain ⟨j, hinj, hζ, hfes⟩ := _root_.GlobalTheory.SiegelTor.exists_inclusion_cycAway n N hN0 hnN
  obtain ⟨hfin, het, hsurj⟩ := hfes hpow
  obtain ⟨Q⟩ := _root_.GlobalTheory.SiegLev.nonempty_sQuot h n N F j hn hN hnN hζ hfin het
  exact ⟨{
    X := Q.X
    s := Q.s
    smooth := Q.smooth
    qproj := Q.qproj
    univ := Q.univ
    princ := Q.princ
    rep := fun S s' c hred hdense hpr =>
      _root_.GlobalTheory.quotFam_represents h n N F j Q hn hN hnN hinj hζ hfin het hsurj S s' c hred hdense hpr
    inj := fun R _ _ x y s' c hs h₁ h₂ =>
      _root_.GlobalTheory.SiegLev.SQuot.eq_of_siegPB h n N _ _ (zetaAway n) (zetaAway N) F j Q R x y s' c hs h₁ h₂ }⟩

end GlobalTheory.SiegLev
