import Mathlib
import GroundTheory.PAdicHodge.WAEval
import GroundTheory.PAdicHodge.UnramifiedFrob

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WAPeriodT

open _root_.WittVector WittTilt PhiGamma TeichLift UniformSpace Laurent WAEval Filter Topology

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔪" => IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p)

variable (p) in

def unitInv (n : ℕ) : ℤ_[p] := ((n / p ^ n.factorization p : ℕ) : ℤ_[p]).inv

variable (p) in

def logCoeff (n : ℕ) : 𝔸 :=
  (-1) ^ (n + 1) * algebraMap (AInf ℂ_[p] p) 𝔸 (IsPerfectoidField.padicIntToWitt p (unitInv p n)) *
    IsLocalization.Away.invSelf (p : AInf ℂ_[p] p) ^ n.factorization p

variable (p) in

def muA (ε : 𝒪♭) : 𝔸 := algebraMap (AInf ℂ_[p] p) 𝔸 (AInf.mu ε)

end WAPeriodT

end GroundTheory.PAdicHodge
