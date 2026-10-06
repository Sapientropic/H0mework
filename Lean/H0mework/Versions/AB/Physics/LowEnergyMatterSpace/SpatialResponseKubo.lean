import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.SpatialResponseEvolution

/-! The actual two-sided spatial current variation equals its causal commutator integral. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
noncomputable section

def heisenberg (observable : MatterL2 →L[ℂ] MatterL2) (t : ℝ) : MatterL2 →L[ℂ] MatterL2 :=
  (freeOperator (-t)).comp (observable.comp (freeOperator t))

theorem heisenberg_apply (observable : MatterL2 →L[ℂ] MatterL2) (t : ℝ) (u : MatterL2) :
    heisenberg observable t u=spatialUnitary (-t) (observable (spatialUnitary t u)) := rfl

theorem heisenberg_one (t : ℝ) : heisenberg 1 t=1 := by
  apply ContinuousLinearMap.ext
  intro u
  change spatialUnitary (-t) (spatialUnitary t u)=u
  rw [← spatialUnitary_add,neg_add_cancel,spatialUnitary_zero]

theorem heisenberg_pair (observable : MatterL2 →L[ℂ] MatterL2) (t : ℝ) (u v : MatterL2) :
    inner ℂ u (heisenberg observable t v)=inner ℂ (spatialUnitary t u) (observable (spatialUnitary t v)) := by
  have paired := spatial_pair_transfer (-t) u (observable (spatialUnitary t v))
  simpa only [heisenberg_apply,neg_neg] using paired.symm

theorem heisenberg_symmetric (observable : MatterL2 →L[ℂ] MatterL2) (symmetric : IsSelfAdjoint observable)
    (t : ℝ) (u v : MatterL2) :
    inner ℂ (heisenberg observable t u) v=inner ℂ u (heisenberg observable t v) := by
  change inner ℂ (spatialUnitary (-t) (observable (spatialUnitary t u))) v=_
  rw [spatial_pair_transfer,heisenberg_pair]
  exact symmetric.isSymmetric _ _

theorem heisenberg_action_continuous (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (u : MatterL2) :
    Continuous (fun s => heisenberg (perturbation s) s u) := by
  simp only [heisenberg_apply]
  have inside := continuousPerturbation.clm_apply (spatialUnitary_stronglyContinuous u)
  have composed := spatialUnitary_joint.comp (continuous_id.neg.prodMk inside)
  simpa only [Function.comp_def,Pi.neg_apply,id_eq] using composed

private theorem inner_integral_left (f : ℝ → MatterL2) (continuousF : Continuous f) (v : MatterL2) (t : ℝ) :
    inner ℂ (∫ s in (0 : ℝ)..t, f s) v=∫ s in (0 : ℝ)..t, inner ℂ (f s) v := by
  have linear := (innerSL ℂ v).intervalIntegral_comp_comm (continuousF.intervalIntegrable (μ := volume) 0 t)
  change (∫ s in (0 : ℝ)..t, inner ℂ v (f s))=inner ℂ v (∫ s in (0 : ℝ)..t, f s) at linear
  calc
    _ = star (inner ℂ v (∫ s in (0 : ℝ)..t, f s)) := (inner_conj_symm _ _).symm
    _ = star (∫ s in (0 : ℝ)..t, inner ℂ v (f s)) := congrArg star linear.symm
    _ = ∫ s in (0 : ℝ)..t, star (inner ℂ v (f s)) :=
      (intervalIntegral.intervalIntegral_conj (f := fun s => inner ℂ v (f s))).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s _
      exact inner_conj_symm _ _

private theorem pointwise_commutator (perturbation current : MatterL2 →L[ℂ] MatterL2)
    (symmetric : ∀ u v, inner ℂ (perturbation u) v=inner ℂ u (perturbation v)) (u : MatterL2) :
    inner ℂ ((-Complex.I) • perturbation u) (current u)+
      inner ℂ u (current ((-Complex.I) • perturbation u))=
      Complex.I*inner ℂ u ((perturbation.comp current-current.comp perturbation) u) := by
  rw [inner_smul_left,map_smul,inner_smul_right,symmetric]
  simp only [map_neg,Complex.conj_I,neg_neg]
  change Complex.I*inner ℂ u (perturbation (current u))+
      (-Complex.I)*inner ℂ u (current (perturbation u))=
    Complex.I*inner ℂ u (perturbation (current u)-current (perturbation u))
  rw [inner_sub_right]
  ring

def kuboKernel (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (current : MatterL2 →L[ℂ] MatterL2) (u : MatterL2) (t s : ℝ) : ℂ :=
  inner ℂ u (((heisenberg (perturbation s) s).comp (heisenberg current t)-
    (heisenberg current t).comp (heisenberg (perturbation s) s)) u)

theorem kuboKernel_continuous (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (current : MatterL2 →L[ℂ] MatterL2)
    (u : MatterL2) (t : ℝ) : Continuous (kuboKernel perturbation current u t) := by
  have left := heisenberg_action_continuous perturbation continuousPerturbation (heisenberg current t u)
  have right := (heisenberg current t).continuous.comp (heisenberg_action_continuous perturbation continuousPerturbation u)
  exact continuous_const.inner (left.sub right)

theorem currentVariation_kubo (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (hermitian : ∀ s, IsSelfAdjoint (perturbation s))
    (current : MatterL2 →L[ℂ] MatterL2) (u : MatterL2) (t : ℝ) :
    currentVariation perturbation current u t=Complex.I*∫ s in (0 : ℝ)..t, kuboKernel perturbation current u t s := by
  let f := interactionForcing (perturbationForce perturbation u)
  have continuousF : Continuous f := interactionForcing_continuous _
    (perturbationForce_continuous perturbation continuousPerturbation u)
  have first := inner_integral_left f continuousF (heisenberg current t u) t
  have second := ((innerSL ℂ u).comp (heisenberg current t)).intervalIntegral_comp_comm
    (continuousF.intervalIntegrable (μ := volume) 0 t)
  change (∫ s in (0 : ℝ)..t, inner ℂ u (heisenberg current t (f s)))=
    inner ℂ u (heisenberg current t (∫ s in (0 : ℝ)..t, f s)) at second
  have integrableLeft : IntervalIntegrable (fun s => inner ℂ (f s) (heisenberg current t u)) volume 0 t :=
    (continuousF.inner continuous_const).intervalIntegrable (μ := volume) 0 t
  have integrableRight : IntervalIntegrable (fun s => inner ℂ u (heisenberg current t (f s))) volume 0 t :=
    (continuous_const.inner ((heisenberg current t).continuous.comp continuousF)).intervalIntegrable (μ := volume) 0 t
  change inner ℂ (spatialUnitary t (∫ s in (0 : ℝ)..t, f s)) (current (spatialUnitary t u))+
    inner ℂ (spatialUnitary t u) (current (spatialUnitary t (∫ s in (0 : ℝ)..t, f s)))=_
  rw [← heisenberg_pair,← heisenberg_pair,first,← second,
    ← intervalIntegral.integral_add integrableLeft integrableRight,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  change inner ℂ (spatialUnitary (-s) ((-Complex.I) • perturbation s (spatialUnitary s u)))
      (heisenberg current t u)+
    inner ℂ u (heisenberg current t (spatialUnitary (-s) ((-Complex.I) • perturbation s (spatialUnitary s u))))=_
  rw [map_smul]
  exact pointwise_commutator (heisenberg (perturbation s) s) (heisenberg current t)
    (heisenberg_symmetric _ (hermitian s) s) u

theorem currentVariation_identity (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (hermitian : ∀ s, IsSelfAdjoint (perturbation s))
    (u : MatterL2) (t : ℝ) : currentVariation perturbation 1 u t=0 := by
  rw [currentVariation_kubo perturbation continuousPerturbation hermitian]
  simp [kuboKernel,heisenberg_one]

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
