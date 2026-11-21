import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.HeightCounting.Up

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

theorem row_mono_id {Bd : GlobalTheory.Fc.BdT} {Q Q₁ : V4.Slot} {Lk Lk₁ : GlobalTheory.Fc.LkT Bd} {H : ∀ 𝒜 : FamClass, GlobalTheory.Fc.RawSel Bd 𝒜 → Prop}
    (hQ : ∀ K X f T c, Q₁ K X f T c → Q K X f T c) (hL : ∀ K β c b, Lk₁ K β c b → Lk K β c b)
    (h : GlobalTheory.Fc.Row Q Lk H) : GlobalTheory.Fc.Row Q₁ Lk₁ H :=
  GlobalTheory.Fc.Row.map (fun _ _ _ b => b) hQ (fun K β c b _ t => hL K β c b t) h

theorem largeBaseProperty_anti {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q₁ R : V4.Slot} (hQ : ∀ K X f T c, Q₁ K X f T c → Q K X f T c)
    (h : GlobalTheory.Fc.LargeBaseCondition KP Q R) : GlobalTheory.Fc.LargeBaseCondition KP Q₁ R :=
  GlobalTheory.Fc.eventuallyAllScaleContexts_mono_of_imp (fun _ H => H.imp fun _ _ _ _ t k C W V S N G c q => t k C W V S N G c (hQ _ _ _ _ _ q)) h

theorem eventually_coreProperty_mono_fewerCores {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q₁ Q' Q'₁ : V4.Slot} {r r₁ : V4.Slot → Prop}
    (hQ : ∀ K X f T c, Q₁ K X f T c → Q K X f T c) (hQ' : ∀ K X f T c, Q'₁ K X f T c → Q' K X f T c)
    (hr : ∀ S S₁ : V4.Slot, (∀ K X f T c, S₁ K X f T c → S K X f T c) → r S → r₁ S₁)
    (h : GlobalTheory.Fc.Lg1 KP Q Q' r) : GlobalTheory.Fc.Lg1 KP Q₁ Q'₁ r₁ := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨R, largeBaseProperty_anti hQ hR, hr _ _ (fun _ _ _ _ _ t => ⟨hQ' _ _ _ _ _ t.1, t.2⟩) h⟩

end GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

end GlobalTheory.HeightCounting.Up
