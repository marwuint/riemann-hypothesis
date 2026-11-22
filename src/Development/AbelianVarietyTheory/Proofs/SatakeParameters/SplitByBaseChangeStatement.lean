import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitByBaseChange

open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitBy_baseChange' : ∀ {Z X V T : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ} {s : Fin m → (V ⟶ Z)}, GlobalTheory.EtC.Tr.SplitBy f y s → ∀ (w : T ⟶ V), GlobalTheory.EtC.Tr.SplitBy f (w ≫ y) (fun j => w ≫ s j) := GlobalTheory.EtC.Tr.splitBy_baseChange
