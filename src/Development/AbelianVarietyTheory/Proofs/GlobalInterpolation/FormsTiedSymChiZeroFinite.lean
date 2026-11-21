import Mathlib
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentTypeLevelCharacterFiniteOrderRootsOfUni
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem formsTiedSym_chi_zero_finite : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), (∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)) → ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U, (((Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ) :=
  fun D _ _ _ Tf h =>
    _root_.GlobalTheory.unipotent_type_character_finite_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Tf.glev0 D.what₂.LL D.what₂.embLL D.host.g_prime (fun i => (h i).1)

end GlobalTheory
