import Mathlib
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Columns.RowForms

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions

section PosX

variable (R : Ranks)

def posXn (i : ℕ) : ℕ :=
  if i < R.k - 1 then i
  else if i < R.r then R.k - 1 + (i - (R.k - 1)) * (R.t + 1)
  else R.k - 1 + ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1)

def invXn (y : ℕ) : ℕ :=
  if y < R.k - 1 then y
  else if (y - (R.k - 1)) % (R.t + 1) = 0 then R.k - 1 + (y - (R.k - 1)) / (R.t + 1)
  else R.r + ((y - (R.k - 1)) / (R.t + 1)) * R.t + ((y - (R.k - 1)) % (R.t + 1) - 1)

theorem nz_t_pos : 0 < R.t := by
  have := R.rank_add_five_le
  omega

theorem nz_r_eq : R.r = R.k - 1 + R.m := by
  have := R.m_add_three_le_k
  unfold Ranks.r
  omega

theorem nz_rankX : R.N R.m - 1 = R.k - 1 + R.m * (R.t + 1) := by
  have := R.m_add_three_le_k
  unfold Ranks.N
  omega

theorem nz_posXn_hi {i : ℕ} (h : R.r ≤ i) :
    posXn R i = R.k - 1 + ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1) := by
  have := nz_r_eq R
  unfold posXn
  rw [if_neg (by omega), if_neg (by omega)]

theorem nz_invXn_posXn (i : ℕ) : invXn R (posXn R i) = i := by
  have hr := nz_r_eq R
  have ht := nz_t_pos R
  by_cases h1 : i < R.k - 1
  · unfold posXn invXn
    rw [if_pos h1, if_pos h1]
  by_cases h2 : i < R.r
  · have e0 : posXn R i = R.k - 1 + (i - (R.k - 1)) * (R.t + 1) := by
      unfold posXn
      rw [if_neg h1, if_pos h2]
    obtain ⟨d1, d2⟩ := divmod (R.t + 1) (i - (R.k - 1)) 0 (by omega)
    have e1 : R.k - 1 + (i - (R.k - 1)) * (R.t + 1) - (R.k - 1) = (i - (R.k - 1)) * (R.t + 1) + 0 := by omega
    unfold invXn
    rw [e0, if_neg (by omega), e1, d1, d2, if_pos rfl]
    omega
  · have hm : (i - R.r) % R.t < R.t := Nat.mod_lt _ ht
    obtain ⟨d1, d2⟩ := divmod (R.t + 1) ((i - R.r) / R.t) ((i - R.r) % R.t + 1) (by omega)
    have e1 : R.k - 1 + ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1) - (R.k - 1) =
        ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1) := by omega
    have e2 := Nat.div_add_mod (i - R.r) R.t
    rw [Nat.mul_comm] at e2
    unfold invXn
    rw [nz_posXn_hi R (Nat.not_lt.mp h2), if_neg (by omega), e1, d1, d2, if_neg (by omega)]
    omega

theorem nz_posXn_lt {i : ℕ} (h : i < R.N R.m - 1) : posXn R i < R.N R.m - 1 := by
  have hr := nz_r_eq R
  have ht := nz_t_pos R
  have hn := nz_rankX R
  have hn' := rank_X'_eq R
  by_cases h1 : i < R.k - 1
  · unfold posXn
    rw [if_pos h1]
    exact h
  by_cases h2 : i < R.r
  · have h3 : (i - (R.k - 1) + 1) * (R.t + 1) ≤ R.m * (R.t + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h3
    unfold posXn
    rw [if_neg h1, if_pos h2]
    omega
  · have hm : (i - R.r) % R.t < R.t := Nat.mod_lt _ ht
    have hd : (i - R.r) / R.t < R.m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have h3 : ((i - R.r) / R.t + 1) * (R.t + 1) ≤ R.m * (R.t + 1) := Nat.mul_le_mul_right _ hd
    rw [Nat.add_mul, Nat.one_mul] at h3
    rw [nz_posXn_hi R (Nat.not_lt.mp h2)]
    omega

def posXf (i : Fin (R.N R.m - 1)) : Fin (R.N R.m - 1) := ⟨posXn R i.1, nz_posXn_lt R i.2⟩

theorem nz_posXf_inj : Function.Injective (posXf R) := by
  intro a b h
  have h1 : posXn R a.1 = posXn R b.1 := congrArg Fin.val h
  apply Fin.ext
  rw [← nz_invXn_posXn R a.1, ← nz_invXn_posXn R b.1, h1]

def posX : Equiv.Perm (Fin (R.N R.m - 1)) :=
  Equiv.ofBijective (posXf R) (Finite.injective_iff_bijective.mp (nz_posXf_inj R))

variable {R}

end PosX

section PosV

variable (R : Ranks) (j : ℕ)

def pV : ℕ := min (RowPar.pOf R j) R.r

def posVn (i : ℕ) : ℕ :=
  if i < pV R j then i else if i < R.r then i + R.t else i - R.r + pV R j

theorem nz_pV_le : pV R j ≤ R.r := min_le_right _ _

theorem nz_posVn_lt {i : ℕ} (h : i < R.nV) : posVn R j i < R.nV := by
  have h1 := nz_pV_le R j
  unfold Ranks.nV at h ⊢
  unfold posVn
  split_ifs <;> omega

def posVf (i : Fin R.nV) : Fin R.nV := ⟨posVn R j i.1, nz_posVn_lt R j i.2⟩

theorem nz_posVf_inj : Function.Injective (posVf R j) := by
  intro a b h
  have h1 : posVn R j a.1 = posVn R j b.1 := congrArg Fin.val h
  have h2 := nz_pV_le R j
  have ha := a.2
  have hb := b.2
  unfold Ranks.nV at ha hb
  apply Fin.ext
  unfold posVn at h1
  split_ifs at h1 <;> omega

def posV : Equiv.Perm (Fin R.nV) :=
  Equiv.ofBijective (posVf R j) (Finite.injective_iff_bijective.mp (nz_posVf_inj R j))

variable {R j}

def sV (R : Ranks) (j : ℕ) : ℚ := ((R.k : ℚ) - (R.m : ℚ)) / 2 + (j : ℚ) - 1

end PosV

end Formalism.L2.Col
