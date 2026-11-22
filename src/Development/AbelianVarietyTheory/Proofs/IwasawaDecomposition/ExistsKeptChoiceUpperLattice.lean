import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongrFunHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowReadingsSameRowsIdentifyDefiniteForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsSameGeometricHalf
import Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000

theorem tupTied_ext {D : D7} {cf : CharFrame D} {C : NChoice D} {p q : TupTied D cf C} (h1 : p.xi = q.xi) (h2 : p.psi = q.psi) :
    p = q := by
  cases p; cases q; cases h1; cases h2; rfl

section
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) {nch : NChoice (w.D Z)}
  {xd : ThData (w.D Z)}

theorem nchT_up (n : NchT w Z Wt nch) : Nonempty (NchT w (upL Z S' N h) Wt (nchUp S' N h nch)) :=
  ⟨{ tp := by kcopy n.tp, xi := kc% n.xi, psi := kc% n.psi, tie := by kcopy n.tie, Q := n.Q, chrPsi := by kcopy n.chrPsi }⟩

theorem kept_up (nch : NChoice (w.D Z)) : Kept nch (nchUp S' N h nch) := by
  refine ⟨?_, ?_, ?_, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩ <;> constructor <;> first | rfl | exact HEq.rfl

theorem goodO_up (g : GoodO (w.D Z) nch xd) : GoodO (w.D (upL Z S' N h)) (nchUp S' N h nch) (xdUp S' N h xd) := by
  obtain ⟨⟨E, N0, S⟩, h1, h2, h3⟩ := g.tw
  cases h1
  exact ⟨⟨⟨twEOf (xdUp S' N h xd), N0, S⟩, rfl, kc% h2, kc% h3⟩, g.sep⟩
end

end GlobalTheory.LayerMove
end
