import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliPrimePowerFullLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyCmModuliOfDeeperLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelWithOddPrimeFirstNumber
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyModuliOfLevelDvd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem moduli_nonempty_all_levels : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N1ab := by
  intro h1 h2 h3 h4 E _ _ _ H D l hD
  obtain ⟨n, hn, hodd, hl⟩ := _root_.GlobalTheory.ZM.exists_prime_level E H l
  obtain ⟨j, hj⟩ := _root_.GlobalTheory.ZM.exists_moduli_prime_power_level h1 h2 h3 h4 E H D n hD hn hodd
  obtain ⟨l₀, l₂, hM, hA, h02, h2'⟩ := hl ((n ^ j) ^ 2) (pow_pos (pow_pos hn.pos j) 2)
  exact _root_.GlobalTheory.ZM.moduli_of_deeper_level h1 h2 h3 E H D l l₂ hD h2'
    (_root_.GlobalTheory.nonempty_moduli_of_dvd h1 h2 E H D l₀ l₂ hD h02 (hj l₀ hM hA))

end GlobalTheory.ZM
