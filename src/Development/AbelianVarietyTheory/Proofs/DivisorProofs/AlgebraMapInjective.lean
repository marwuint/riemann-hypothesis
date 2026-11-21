import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSimR

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

namespace GlobalTheory.CentAtP

variable {p : ℕ} [Fact p.Prime]

variable {G : HTGroup p} {P : Pair G}

theorem mem_simT_iff {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A] {c : A →ₐ[k] A} {x : Aˣ} :
    x ∈ GlobalTheory.LKTorus.simT k c ↔ ∃ t : kˣ, (x : A) * c x = algebraMap k A t := Iff.rfl

end GlobalTheory.CentAtP
