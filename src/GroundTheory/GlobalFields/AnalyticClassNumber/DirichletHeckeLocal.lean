import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup Topology
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace DirichletHecke

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract RationalSymbol

theorem proj_eq_of_forall {N : ℕ} [NeZero N] {z : ℤ̂} {a : ZMod N}
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), prime v ∣ N →
      PadicInt.toZModPow (N.factorization (prime v)) (toPadicInt (prime v) z) =
        ZMod.castHom (Nat.ordProj_dvd N (prime v)) _ a) :
    ProfiniteInteger.proj (modulus N) z = a := by
  refine eq_of_castHom_ordProj_eq (NeZero.ne N) fun p hp ↦ ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hv : prime (placeOf ⟨p, hpp⟩) = p := prime_placeOf ⟨p, hpp⟩
  have hdvd : prime (placeOf ⟨p, hpp⟩) ∣ N := by
    rw [hv]
    exact Nat.dvd_of_mem_primeFactors hp
  have h' := h (placeOf ⟨p, hpp⟩) hdvd
  clear hdvd
  generalize placeOf ⟨p, hpp⟩ = v at hv h'
  subst hv
  rw [toZModPow_toPadicInt] at h'
  rw [← h']
  exact ProfiniteInteger.castHom_proj (m := primePowPNat (prime v) (N.factorization (prime v)))
    (n := modulus N) (Nat.ordProj_dvd N (prime v)) z

theorem mem_adicCompletionIntegers_of_norm_le (v : HeightOneSpectrum (𝓞 ℚ)) {x : v.adicCompletion ℚ}
    (hx : ‖padicRingEquiv v x‖ ≤ 1) : x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨y, hy, hyx⟩ := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).surjOn
    ((PadicInt.mem_subring_iff _).2 hx)
  have : y = x := (padicRingEquiv v).injective hyx
  exact this ▸ hy

theorem mem_positiveSubgroup_of {x : IdeleGroup ℚ}
    (hfin : ∀ w : HeightOneSpectrum (𝓞 ℚ), ‖padicRingEquiv w (finiteProj w x : w.adicCompletion ℚ)‖ = 1)
    (hre : 0 < (RationalIdeles.realPart x : ℝ)) : x ∈ RationalIdeles.positiveSubgroup := by
  refine RationalIdeles.mem_positiveSubgroup.2 ⟨(mem_standardOpenSubgroup ℚ).2 fun w ↦ ⟨?_, ?_⟩, hre⟩
  · rw [← coe_finiteProj]
    exact mem_adicCompletionIntegers_of_norm_le w (hfin w).le
  · rw [← coe_finiteProj, map_inv, Units.val_inv_eq_inv_val]
    refine mem_adicCompletionIntegers_of_norm_le w ?_
    rw [map_inv₀, norm_inv, hfin w, inv_one]

theorem realPart_finiteEmbedding (v : HeightOneSpectrum (𝓞 ℚ)) (a : (v.adicCompletion ℚ)ˣ) :
    RationalIdeles.realPart (finiteEmbedding v a) = 1 := by
  change RationalIdeles.realUnitsEquiv.toMulEquiv.toMonoidHom (toInfinite ℚ (finiteEmbedding v a)) = 1
  rw [toInfinite_finiteEmbedding, map_one]

theorem coe_unitAt (y : RationalIdeles.positiveSubgroup) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (((unitAt y v : ℤ_[prime v]ˣ) : ℤ_[prime v]) : ℚ_[prime v]) =
      padicRingEquiv v (finiteProj v (y : IdeleGroup ℚ) : v.adicCompletion ℚ) := by
  rw [padicRingEquiv_finiteProj, pow_zero, mul_one]

theorem toPadicInt_unitPart_inv_mk (y : RationalIdeles.positiveSubgroup) (v : HeightOneSpectrum (𝓞 ℚ)) :
    toPadicInt (prime v) (((unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)))⁻¹ : ℤ̂ˣ) : ℤ̂) =
      (((unitAt y v)⁻¹ : ℤ_[prime v]ˣ) : ℤ_[prime v]) := by
  have h' : Units.map (toPadicInt (prime v)).toMonoidHom
      (unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ))) = unitAt y v :=
    Units.ext (toPadicInt_unitPart_mk y v)
  rw [← h', Units.coe_map_inv]
  rfl

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

theorem coe_heckeCharacter_mk_of_forall (y : RationalIdeles.positiveSubgroup) {a : ZMod N}
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), prime v ∣ N →
      PadicInt.toZModPow (N.factorization (prime v)) (((unitAt y v)⁻¹ : ℤ_[prime v]ˣ) : ℤ_[prime v]) =
        ZMod.castHom (Nat.ordProj_dvd N (prime v)) _ a) :
    (heckeCharacter χ (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) : ℂ) = χ a := by
  rw [coe_heckeCharacter_apply, proj_eq_of_forall fun v hv ↦ by
    rw [toPadicInt_unitPart_inv_mk]
    exact h v hv]

theorem norm_padicRingEquiv_eq_one {v : HeightOneSpectrum (𝓞 ℚ)} {a : (v.adicCompletion ℚ)ˣ}
    (ha : a ∈ (Submonoid.ofClass (v.adicCompletionIntegers ℚ)).units) :
    ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1 := by
  obtain ⟨h1, h2⟩ := (Submonoid.mem_units_iff _ _).1 ha
  have n1 : ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ ≤ 1 :=
    (PadicInt.mem_subring_iff _).1 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo h1)
  have n2 : ‖padicRingEquiv v ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ ≤ 1 :=
    (PadicInt.mem_subring_iff _).1 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo h2)
  rw [Units.val_inv_eq_inv_val, map_inv₀, norm_inv] at n2
  have hpos : 0 < ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ :=
    norm_pos_iff.2 ((map_ne_zero _).2 a.ne_zero)
  exact le_antisymm n1 ((inv_le_one₀ hpos).1 n2)

theorem finiteEmbedding_mem_positiveSubgroup {v : HeightOneSpectrum (𝓞 ℚ)} {a : (v.adicCompletion ℚ)ˣ}
    (ha : ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1) :
    finiteEmbedding v a ∈ RationalIdeles.positiveSubgroup := by
  refine mem_positiveSubgroup_of (fun w ↦ ?_) (by rw [realPart_finiteEmbedding, Units.val_one]; exact one_pos)
  by_cases hw : w = v
  · subst hw
    rw [finiteProj_finiteEmbedding]
    exact ha
  · rw [finiteProj_finiteEmbedding_of_ne hw, Units.val_one, map_one, norm_one]

theorem unitAt_eq_one {y : RationalIdeles.positiveSubgroup} {w : HeightOneSpectrum (𝓞 ℚ)}
    (h : finiteProj w (y : IdeleGroup ℚ) = 1) : unitAt y w = 1 :=
  Units.ext (Subtype.ext (by rw [coe_unitAt, h, Units.val_one, map_one, Units.val_one, PadicInt.coe_one]))

theorem heckeCharacter_finiteEmbedding_of_not_dvd {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ¬ prime v ∣ N)
    {a : (v.adicCompletion ℚ)ˣ} (ha : ‖padicRingEquiv v (a : v.adicCompletion ℚ)‖ = 1) :
    heckeCharacter χ (IdeleClassGroup.mk ℚ (finiteEmbedding v a)) = 1 := by
  refine Circle.ext ?_
  rw [Circle.coe_one, ← map_one χ]
  refine coe_heckeCharacter_mk_of_forall χ ⟨_, finiteEmbedding_mem_positiveSubgroup ha⟩ fun w hw ↦ ?_
  have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
  rw [unitAt_eq_one (finiteProj_finiteEmbedding_of_ne hwv a), inv_one, Units.val_one, map_one, map_one]

def uniformizer (v : HeightOneSpectrum (𝓞 ℚ)) : (v.adicCompletion ℚ)ˣ :=
  finiteProj v (diagonal ℚ (primeRat v))

theorem asIdeal_eq_span (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {((prime v : ℕ) : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator v
  have h' : v.asIdeal = (v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))).map
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm := (Ideal.map_of_equiv _).symm
  rw [h', ← h, Ideal.map_span, Set.image_singleton, map_natCast]
  rfl

theorem valued_uniformizer (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (uniformizer v : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [uniformizer, coe_finiteProj_diagonal, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    coe_primeRat, show ((prime v : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((prime v : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _
    (Nat.cast_ne_zero.2 (Fact.out : (prime v).Prime).ne_zero) (asIdeal_eq_span v)

theorem frobIdele_mem (v : HeightOneSpectrum (𝓞 ℚ)) :
    (diagonal ℚ (primeRat v))⁻¹ * finiteEmbedding v (uniformizer v) ∈
      RationalIdeles.positiveSubgroup := by
  refine mem_positiveSubgroup_of (fun w ↦ ?_) ?_
  · by_cases hw : w = v
    · subst hw
      rw [map_mul, map_inv, finiteProj_finiteEmbedding, uniformizer, inv_mul_cancel, Units.val_one,
        map_one, norm_one]
    · rw [map_mul, map_inv, finiteProj_finiteEmbedding_of_ne hw, mul_one, Units.val_inv_eq_inv_val,
        map_inv₀, norm_inv, padicRingEquiv_finiteProj_diagonal, coe_primeRat, Rat.cast_natCast,
        Padic.norm_natCast_eq_one_iff.2 (coprime_prime hw), inv_one]
  · rw [map_mul, map_inv, realPart_finiteEmbedding, mul_one, Units.val_inv_eq_inv_val,
      RationalIdeles.realPart_diagonal, coe_primeRat]
    exact inv_pos.2 (by exact_mod_cast (Fact.out : (prime v).Prime).pos)

theorem proj_unitPart_inv_uniformizer {N : ℕ} [NeZero N] {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ¬ prime v ∣ N) :
    ProfiniteInteger.proj (modulus N)
      (((unitPart (IdeleClassGroup.mk ℚ (finiteEmbedding v (uniformizer v))))⁻¹ : ℤ̂ˣ) : ℤ̂) =
      (prime v : ZMod N) := by
  let y : RationalIdeles.positiveSubgroup := ⟨_, frobIdele_mem v⟩
  have hmk : IdeleClassGroup.mk ℚ (finiteEmbedding v (uniformizer v)) =
      IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ) := by
    show _ = IdeleClassGroup.mk ℚ ((diagonal ℚ (primeRat v))⁻¹ * finiteEmbedding v (uniformizer v))
    rw [map_mul, map_inv, IdeleClassGroup.mk_diagonal, inv_one]
    exact (one_mul (IdeleClassGroup.mk ℚ (finiteEmbedding v (uniformizer v)))).symm
  rw [hmk]
  refine proj_eq_of_forall fun w hw ↦ ?_
  have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
  have e1 : (((unitAt y w : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) = ((prime v : ℚ_[prime w]))⁻¹ := by
    rw [coe_unitAt]
    simp only [y, map_mul, map_inv, finiteProj_finiteEmbedding_of_ne hwv, mul_one,
      Units.val_inv_eq_inv_val, map_inv₀, padicRingEquiv_finiteProj_diagonal, coe_primeRat,
      Rat.cast_natCast]
  have e2 : ((((unitAt y w)⁻¹ : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) *
      (((unitAt y w : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) = 1 := by
    rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
  have hp0 : (prime v : ℚ_[prime w]) ≠ 0 :=
    Nat.cast_ne_zero.2 (Fact.out : (prime v).Prime).ne_zero
  have hu : (((unitAt y w)⁻¹ : ℤ_[prime w]ˣ) : ℤ_[prime w]) = (prime v : ℤ_[prime w]) := by
    apply Subtype.ext
    rw [e1] at e2
    rw [PadicInt.coe_natCast]
    exact (mul_inv_eq_one₀ hp0).1 e2
  rw [toPadicInt_unitPart_inv_mk, hu, map_natCast, map_natCast]

theorem coe_heckeCharacter_uniformizer {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ¬ prime v ∣ N) :
    (heckeCharacter χ (IdeleClassGroup.mk ℚ (finiteEmbedding v (uniformizer v))) : ℂ) = χ (prime v) := by
  rw [coe_heckeCharacter_apply, proj_unitPart_inv_uniformizer hv]

end DirichletHecke

end

end GroundTheory.Global
