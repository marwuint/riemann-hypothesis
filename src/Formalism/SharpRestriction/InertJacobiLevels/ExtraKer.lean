import Formalism.LocalRingCardinality.DataKerP
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.LocalRingCardinality.SpanPowerMembership.ClassRecordRowDimensionZero

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

structure ServedEmb (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    [Fact (D.what₂.places.resChar w).Prime] (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) where
  iLL : D.what₂.LL →+* (D.gat u w h).Kf
  iLL_w : ∀ x : D.what₂.LL, (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
    iLL x ∈ Set.range (algebraMap (D.gat u w h).O (D.gat u w h).Kf)
  iK : (D.gat u w h).Kf →+* ℂ_[D.what₂.places.resChar w]
  iw : ∀ v : Fin (D.gat u w h).P.nV, D.host.E →+* (D.gat u w h).P.Qq v
  glob : (D.gat u w h).P.Tup → Submodule (𝓞 D.host.E) (Fin ((D.gat u w h).P.m + 1) → D.host.E)
  glob_loc : ∀ L : (D.gat u w h).P.Tup, (D.gat u w h).P.IsLatTup L → ∀ v,
    L v = Submodule.span ((D.gat u w h).P.W v) {y | ∃ x ∈ glob L, y = fun i => iw v (x i)}

section Tw

def atTZ {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (T : ℕ) (hT : T.Prime) :
    ColumnsAtT R C :=
  haveI : NeZero T := ⟨hT.ne_zero⟩
  haveI : Fact T.Prime := ⟨hT⟩
  { T := T
    T_prime := hT
    vT := Fin R.f
    card_vT := Fintype.card_fin _
    Fv := fun _ => ZMod T
    card_Fv := fun _ => ZMod.card T
    psiT := fun _ => ZMod.stdAddChar
    psiT_ne := fun _ => by
      have := ZMod.isPrimitive_stdAddChar T (one_ne_zero (α := ZMod T))
      rwa [AddChar.mulShift_one] at this
    rhoT := fun _ => 1
    Mu0 := ⊥
    Mu0_fd := inferInstance
    Mu0_stable := fun _ _ => by simp
    duStar := 1
    duStar_pos := one_pos
    Dstar := 1
    Dstar_pos := one_pos
    GamP := 2
    one_lt_gammaP := one_lt_two }

theorem heq_fun_of_chain_eq {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C C' : ColumnChain R ι hc}
    (h : C = C') (j : ℕ) [IsEmpty (C.Y j)] (a : C.cls j → C.Y j → ℂ) (b : C'.cls j → C'.Y j → ℂ) : HEq a b := by
  subst h
  exact heq_of_eq (funext fun _ => funext fun y => isEmptyElim y)

instance formsY_sub {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (embLL : LL →+* ℂ)
    (Pl : Rows.Places LL) {Tau : Type} [Fintype Tau] (hTau : Fintype.card Tau = R.f)
    {hc : Tau → HCParam R} (C : ColumnChain R Tau hc) [∀ i, IsEmpty (C.Y i)]
    (A : ColumnsAtT R C) (P : PeriodMap R C) (j : ℕ) : Subsingleton ((Examples₂.formsY embLL Pl hTau C A P).lat j).V :=
  inferInstanceAs (Subsingleton (Examples₂.fmZeroHLat LL).V)

def twFormsZero (D : D7) [∀ u μ i, IsEmpty ((D.chTw u μ).Y i)] [∀ u j, Subsingleton ((D.fm u).lat j).V] :
    TwForms D where
  A := fun u μ => atTZ (D.chTw u μ) (D.mem u).A.T (D.mem u).A.T_prime
  A_T := fun _ _ => rfl
  fm := fun u μ => Examples₂.formsY D.what₂.embLL D.what₂.places D.what₂.card_Tau (D.chTw u μ) _ (D.PTw u μ)
  e0 := fun _ _ => LinearEquiv.ofSubsingleton _ _
  twist_preserves_base_lattice := fun _ _ x => by
    rw [Subsingleton.elim x 0, map_zero]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  embed_mul_block_embedding := fun _ _ _ => funext fun _ => funext fun y => isEmptyElim y
  eMu0 := fun _ _ _ => LinearEquiv.ofSubsingleton _ _
  eMu0_lat := fun _ _ _ x => by
    rw [Subsingleton.elim x 0, map_zero]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  eMu0_emb := fun u j _ _ => heq_fun_of_chain_eq (D.memberColumns_twistedChain_base u) j _ _

instance twFormsZero_sub (D : D7) [∀ u μ i, IsEmpty ((D.chTw u μ).Y i)] [∀ u j, Subsingleton ((D.fm u).lat j).V]
    (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) : Subsingleton (((twFormsZero D).fm u μ).lat j).V :=
  inferInstanceAs (Subsingleton (Examples₂.fmZeroHLat D.what₂.LL).V)

end Tw

end Formalism.MainNotions.Inhab

end
