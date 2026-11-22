import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P.S3x2

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [CommRing A]

variable {c : ι → ℕ} {x y : Matrix ι ι A}

noncomputable def toGL (x : Matrix ι ι A) (h : IsUnit x.det) : GL ι A := Matrix.nonsingInvUnit x h

@[simp] theorem coe_toGL (x : Matrix ι ι A) (h : IsUnit x.det) : (toGL x h : Matrix ι ι A) = x := rfl

end Generic

section Specific

variable {A : Type} [CommRing A] {r k : ℕ}

theorem hEmb_mul (h h' : Matrix (Fin k) (Fin k) A) : hEmb r (h * h') = hEmb r h * hEmb r h' := by
  simp [hEmb, midEmb, Matrix.fromBlocks_multiply]

theorem hEmb_one : hEmb r (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  simp [hEmb, midEmb]

variable (A r k) in

def hEmbHom : Matrix (Fin k) (Fin k) A →* Matrix (Idx r k) (Idx r k) A where
  toFun := hEmb r
  map_one' := hEmb_one
  map_mul' := hEmb_mul

variable (A r k) in

def phi : GL (Fin k) A →* GL (Idx r k) A := Units.map (hEmbHom A r k)

@[simp] theorem coe_phi (h : GL (Fin k) A) :
    (phi A r k h : Matrix (Idx r k) (Idx r k) A) = hEmb r (h : Matrix (Fin k) (Fin k) A) := rfl

end Specific

section Local

variable (o : Type) [CommRing o] [IsLocalRing o]

local notation "𝔽" => IsLocalRing.ResidueField o

variable {o} {r k : ℕ}

end Local

end Formalism.FourierDecayAlt.P.S3x2

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
