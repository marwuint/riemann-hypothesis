import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidOfFreeOfCrystallineDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineDeRhamAbelianStructureOfStatements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual

set_option autoImplicit false

namespace GlobalTheory

theorem abelianDeRham_of_crystallineSmoothLift : GlobalTheory.Published.CrystallineSmoothLift →
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
    GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham := by
  intro hL hH hC hD hP
  obtain ⟨⟨hfree, hhodge, hbc⟩, hcrys⟩ := _root_.GlobalTheory.Published.abelianDeRhamStructure_crystallineDeRham_of_hypotheses hL hH
  have hF : GlobalTheory.Published.AbelianDeRham.Free := GlobalTheory.AbelianPrim.abelianDeRham_free hfree
  exact ⟨hF, hhodge, hbc,
    GlobalTheory.Published.AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hcrys,
    _root_.GlobalTheory.CubeDual.abelianDeRham_duality hC hD hP hF⟩

end GlobalTheory
