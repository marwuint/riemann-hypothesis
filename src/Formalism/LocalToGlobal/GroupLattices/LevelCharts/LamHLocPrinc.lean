import Formalism.LocalToGlobal.GroupLattices.LevelCharts.PsiZeroNontrivialCharacter

noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

section Loc

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}

def HLoc (H : Subgroup (GL (Fin N) (resV F v))) : Subgroup (GL (Fin N) (v.adicCompletion F)) :=
  congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) H

def lamHLoc {Z : Type} [CommGroup Z] (H : Subgroup (GL (Fin N) (resV F v))) (lam : H →* Z) : HLoc F v H →* Z :=
  congChar _ (algMapV_injective F v) _ _ lam

theorem JLoc_eq_HLoc (a t : ℕ) (fixLast : Bool) (fc : ℕ) :
    JLoc F v N a t fixLast fc = HLoc F v (JBar (resV F v) N a t fixLast fc) := rfl

end Loc

section Uni

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (v : HeightOneSpectrum (𝓞 F))
  (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) (fr : GL (Fin N) (v.adicCompletion F))

def HU (H : Subgroup (GL (Fin N) (resV F v))) : Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)) :=
  UPts σE J (v.adicCompletion F) ⊓ (HLoc F v H).comap (toFr v spl fr)

def lamHU {Z : Type} [CommGroup Z] (H : Subgroup (GL (Fin N) (resV F v))) (lam : H →* Z) : HU σE J v spl fr H →* Z :=
  (lamHLoc F v H lam).comp (((toFr v spl fr).subgroupComap (HLoc F v H)).comp (Subgroup.inclusion inf_le_right))

theorem JU_eq_HU (a t : ℕ) (fixLast : Bool) (fc : ℕ) :
    JU σE J v spl fr a t fixLast fc = HU σE J v spl fr (JBar (resV F v) N a t fixLast fc) := rfl

theorem lamU_eq_lamHU {Z : Type} [CommGroup Z] (a t : ℕ) (fixLast : Bool) (fc : ℕ) (ψ0 : AddChar (resV F v) Z)
    (χ : ℕ → (resV F v)ˣ →* Z) (Sd : Finset ℕ) (nb : ℕ) :
    lamU σE J v spl fr a t fixLast fc ψ0 χ Sd nb =
      lamHU σE J v spl fr (JBar (resV F v) N a t fixLast fc) (lamBar (resV F v) N a t fixLast fc ψ0 χ Sd nb) := rfl

end Uni

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

structure LevAtGH (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (gp : Fin 2 → ℕ)
    (splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (Lb : Submodule (𝓞 E) (Fin N → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))
    (H : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin N) (resV F v))) where

  frG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → GL (Fin N) (v.adicCompletion F)

  frG_lat : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (x : Fin N → v.adicCompletion F),
    (∃ y ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb,
      ∀ b, (splitG i v h (y b)).1 = x b) ↔
      ∀ b, (((frG i v h)⁻¹ : GL (Fin N) (v.adicCompletion F)) : Matrix (Fin N) (Fin N) (v.adicCompletion F)).mulVec x b ∈
        v.adicCompletionIntegers F

  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
    Uloc v = HU σE J v (splitG i v h) (frG i v h) (H i v h)

variable {σE : E →ₐ[F] E} {J : Matrix (Fin N) (Fin N) E} {gp : Fin 2 → ℕ}
    {splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    {Lb : Submodule (𝓞 E) (Fin N → E)}
    {Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))}
    {H : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin N) (resV F v))}
    {Z : Type} [CommGroup Z]

def LevAtG.toH {k m t j : ℕ} (X : LevAtG σE J gp splitG Lb Uloc k m t j) :
    LevAtGH σE J gp splitG Lb Uloc (fun _ v _ => JXbar (resV F v) N k m t j) where
  frG := X.frG
  frG_lat := X.frG_lat
  Uloc_g := X.Uloc_g

def LevAtGH.lamV (X : LevAtGH σE J gp splitG Lb Uloc H) (lam : ∀ i v h, H i v h →* Z) (i : Fin 2)
    (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) : Uloc v →* Z :=
  (lamHU σE J v (splitG i v h) (X.frG i v h) (H i v h) (lam i v h)).comp (Subgroup.inclusion (le_of_eq (X.Uloc_g i v h)))

def LevAtGH.lamGlob (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z)
    (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hUp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      Up ≤ (Uloc v).comap (bc (prV (E := E) v))) : Up →* Z :=
  ∏ i : Fin 2, prodChar (placesOver F (gp i)) Uloc
    (fun v hv => X.lamV lam i v ((mem_placesOver F (gp i) (hg i) v).1 hv))
    Up (fun v hv => hUp i v ((mem_placesOver F (gp i) (hg i) v).1 hv))

theorem LevAtG.toH_lamGlob {k m t j : ℕ} (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0)
    (ψ0 : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → AddChar (resV F v) Z)
    (χ : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ℕ → (resV F v)ˣ →* Z)
    (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hUp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      Up ≤ (Uloc v).comap (bc (prV (E := E) v))) :
    X.toH.lamGlob hg (fun i v h => lamXbar (resV F v) N k m t j (ψ0 i v h) (χ i v h)) Up hUp = X.lamGlob hg ψ0 χ Up hUp := rfl

def LevAtGH.lamG (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z :=
  X.lamGlob hg lam (awayG σE J Uloc p) (fun i v h => awayG_le_comap p v (not_mem_of_coprime (hp i) v h))

def LevAtGH.typeX (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z := (X.lamG hg lam p hp)⁻¹

def CharsG.lamX (ch : CharsG F gp Z) (N k m t j : ℕ) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) :
    JXbar (resV F v) N k m t j →* Z := lamXbar (resV F v) N k m t j (ch.psi0 i v h) (ch.chi i v h)

theorem LevAtG.toH_typeX {k m t j : ℕ} (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0) (ch : CharsG F gp Z)
    (p : ℕ) (hp : ∀ i, Nat.Coprime p (gp i)) : X.toH.typeX hg (ch.lamX N k m t j) p hp = X.typeX hg ch p hp := rfl

end Formalism.L2.G
