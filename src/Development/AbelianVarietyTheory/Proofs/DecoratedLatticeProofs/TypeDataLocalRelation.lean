import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataLines
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.UnrWeil

theorem natCast_mem_of_isConjPl {D : D7} (n : ℕ) {PP PP' : Formalism.L2.DIV.Pl D.host.E} (h : Lev.IsConjPl PP' PP)
    (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  by_contra hn'
  obtain ⟨y, c, hc, hyc⟩ := PP'.isMaximal.exists_inv hn'
  obtain ⟨c', hc', e⟩ := h c hc
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have key : (1 : 𝓞 D.host.E) = RingOfIntegers.mapRingHom (starRingEnd D.host.E) y * ((n : ℕ) : 𝓞 D.host.E) + c' := by
    have h1 := congrArg (fun z : 𝓞 D.host.E => star (algebraMap (𝓞 D.host.E) D.host.E z)) hyc
    simp only [map_add, map_mul, map_natCast, map_one, star_add, star_mul', star_natCast, star_one] at h1
    have hy : algebraMap (𝓞 D.host.E) D.host.E (RingOfIntegers.mapRingHom (starRingEnd D.host.E) y) =
        star (algebraMap (𝓞 D.host.E) D.host.E y) := rfl
    have hc2 : algebraMap (𝓞 D.host.E) D.host.E c' = star (algebraMap (𝓞 D.host.E) D.host.E c) := e
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    simp only [map_add, map_mul, map_natCast, map_one, hy, hc2]
    rw [← h1]
  rw [key]
  exact PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ hn) hc'

theorem not_both_mem {D : D7} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (PP : Formalism.L2.DIV.Pl D.host.E)
    (h1 : ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime ((p : ℕ) : 𝓞 D.host.E) ((q : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left a h1) (PP.asIdeal.mul_mem_left b h2)))

end GlobalTheory.Fam.UnrWeil

