import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual GlobalTheory.WeilDeligne GlobalTheory.LFun GlobalTheory.PRep UpperTheory.V.Af.Gu

private theorem sat_of_equiv {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (e : ρ.Equiv ρ') {B : Multiset ℂˣ} (h : HasSatGL w ρ B) : HasSatGL w ρ' B := by
  have he : ∀ g v, e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) := fun g v =>
    e.toIntertwiningMap.isIntertwining _ _ g v
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    have h1 := hx.map e.toLinearEquiv.toLinearMap he ((map_ne_zero_iff _ e.toLinearEquiv.injective).2 hx.1)
    exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
    refine (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => e.toLinearEquiv.injective ?_) fun hx => h0 (by rw [hx, map_zero])).map
      e.toLinearEquiv.toLinearMap he h0
    rw [he]
    exact GlobalTheory.LGrp.mem_fixed.1 hy k hk

