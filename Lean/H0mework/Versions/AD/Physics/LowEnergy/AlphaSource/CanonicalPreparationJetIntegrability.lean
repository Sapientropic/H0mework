import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationJetFrequencyBounds

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumJetDecay
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumFourierJets
open PreparationVacuumMomentumFirst PreparationVacuumTaylor PreparationVacuumRemainder
open CanonicalPreparationSquareCutoff MeasureTheory Filter Set
open scoped ContDiff Topology SchwartzMap FourierTransform RealInnerProductSpace BigOperators
attribute [local irreducible] partialFourier partialFourierJet symbolSlice sourceMomentumJet

theorem partialFourierJet_joint_measurable (n : ℕ) :
    StronglyMeasurable (fun w : PhysicalMomentum × PhysicalMomentum => partialFourierJet n w.1 w.2) := by
  have phase : Continuous (fun w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum =>
      -⟪w.2,w.1.2⟫) :=
    (continuous_snd.inner (continuous_snd.comp continuous_fst)).neg
  have actual : Continuous (fun w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum =>
      𝐞 (-⟪w.2,w.1.2⟫) • sourceMomentumJet n (w.2,w.1.1)) :=
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp phase)).smul
      ((sourceMomentumJet_smooth n).continuous.comp
        (continuous_snd.prodMk (continuous_fst.comp continuous_fst)))
  have integrated := actual.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure PhysicalMomentum))
  simpa only [partialFourierJet_literal,sourceMomentumJet] using! integrated

private theorem shifted_jet_measurable (n : ℕ) (t : ℝ) (p : PhysicalMomentum)
    (q k : (PhysicalMomentum × PhysicalMomentum) → PhysicalMomentum)
    (v : (PhysicalMomentum × PhysicalMomentum) → Fin n → PhysicalMomentum)
    (hq : Continuous q) (hk : Continuous k) (hv : Continuous v) :
    StronglyMeasurable (fun w => partialFourierJet n (p+t • q w) (k w) (v w)) := by
  have shift : Continuous (fun w : PhysicalMomentum × PhysicalMomentum => p+t • q w) :=
    continuous_const.add (hq.const_smul t)
  have jet : StronglyMeasurable
      (fun w : PhysicalMomentum × PhysicalMomentum => partialFourierJet n (p+t • q w) (k w)) :=
    (partialFourierJet_joint_measurable n).comp_measurable (shift.prodMk hk).measurable
  have evaluation : Continuous (fun w : MomentumJet n × (Fin n → PhysicalMomentum) => w.1 w.2) :=
    continuous_eval
  exact evaluation.comp_stronglyMeasurable (jet.prodMk hv.stronglyMeasurable)

theorem shiftedFirst_left_measurable (t : ℝ) (p : PhysicalMomentum) :
    StronglyMeasurable (fun w : PhysicalMomentum × PhysicalMomentum =>
      shiftedFirst p (Real.pi • w.2) w.1 t) := by
  have actual := shifted_jet_measurable 1 t p (fun w => Real.pi • w.2) Prod.fst
    (fun w _ => Real.pi • w.2) (continuous_snd.const_smul Real.pi) continuous_fst
    (continuous_pi fun _ => continuous_snd.const_smul Real.pi)
  simpa only [partialFourierJet_readback,iteratedFDeriv_one_apply,shiftedFirst] using actual

theorem shiftedFirst_right_measurable (t : ℝ) (p : PhysicalMomentum) :
    StronglyMeasurable (fun w : PhysicalMomentum × PhysicalMomentum =>
      shiftedFirst p (-Real.pi • w.1) w.2 t) := by
  have actual := shifted_jet_measurable 1 t p (fun w => -Real.pi • w.1) Prod.snd
    (fun w _ => -Real.pi • w.1) (continuous_fst.const_smul (-Real.pi)) continuous_snd
    (continuous_pi fun _ => continuous_fst.const_smul (-Real.pi))
  simpa only [partialFourierJet_readback,iteratedFDeriv_one_apply,shiftedFirst] using actual

theorem shiftedSecond_left_measurable (t : ℝ) (p : PhysicalMomentum) :
    StronglyMeasurable (fun w : PhysicalMomentum × PhysicalMomentum =>
      shiftedSecond p (Real.pi • w.2) w.1 t) := by
  have actual := shifted_jet_measurable 2 t p (fun w => Real.pi • w.2) Prod.fst
    (fun w _ => Real.pi • w.2) (continuous_snd.const_smul Real.pi) continuous_fst
    (continuous_pi fun _ => continuous_snd.const_smul Real.pi)
  simpa only [partialFourierJet_readback,iteratedFDeriv_two_apply,shiftedSecond] using actual

theorem shiftedSecond_right_measurable (t : ℝ) (p : PhysicalMomentum) :
    StronglyMeasurable (fun w : PhysicalMomentum × PhysicalMomentum =>
      shiftedSecond p (-Real.pi • w.1) w.2 t) := by
  have actual := shifted_jet_measurable 2 t p (fun w => -Real.pi • w.1) Prod.snd
    (fun w _ => -Real.pi • w.1) (continuous_fst.const_smul (-Real.pi)) continuous_snd
    (continuous_pi fun _ => continuous_fst.const_smul (-Real.pi))
  simpa only [partialFourierJet_readback,iteratedFDeriv_two_apply,shiftedSecond] using actual

private theorem shiftedFactor_left_measurable (t : ℝ) (p : PhysicalMomentum) :
    StronglyMeasurable (fun w : PhysicalMomentum × PhysicalMomentum =>
      shiftedFactor p (Real.pi • w.2) w.1 t) :=
  partialFourier_joint_measurable.comp_measurable
    (((continuous_const.add ((continuous_snd.const_smul Real.pi).const_smul t)).prodMk continuous_fst).measurable)

private theorem shiftedFactor_right_measurable (t : ℝ) (p : PhysicalMomentum) :
    StronglyMeasurable (fun w : PhysicalMomentum × PhysicalMomentum =>
      shiftedFactor p (-Real.pi • w.1) w.2 t) :=
  partialFourier_joint_measurable.comp_measurable
    (((continuous_const.add ((continuous_fst.const_smul (-Real.pi)).const_smul t)).prodMk continuous_snd).measurable)

theorem compositionFirstIntegrand_measurable (t : ℝ) (z p : PhysicalMomentum) :
    StronglyMeasurable (compositionFirstIntegrand t z p) := by
  have phase : Continuous (fun w : PhysicalMomentum × PhysicalMomentum => ⟪z,w.1+w.2⟫) :=
    continuous_const.inner (continuous_fst.add continuous_snd)
  exact (continuous_subtype_val.comp (Real.continuous_fourierChar.comp phase)).stronglyMeasurable.smul
    (((shiftedFirst_left_measurable t p).mul (shiftedFactor_right_measurable t p)).add
      ((shiftedFactor_left_measurable t p).mul (shiftedFirst_right_measurable t p)))

theorem compositionSecondIntegrand_measurable (t : ℝ) (z p : PhysicalMomentum) :
    StronglyMeasurable (compositionSecondIntegrand t z p) := by
  have phase : Continuous (fun w : PhysicalMomentum × PhysicalMomentum => ⟪z,w.1+w.2⟫) :=
    continuous_const.inner (continuous_fst.add continuous_snd)
  exact (continuous_subtype_val.comp (Real.continuous_fourierChar.comp phase)).stronglyMeasurable.smul
    ((((shiftedSecond_left_measurable t p).mul (shiftedFactor_right_measurable t p)).add
      (((shiftedFirst_left_measurable t p).mul (shiftedFirst_right_measurable t p)).const_mul 2)).add
      ((shiftedFactor_left_measurable t p).mul (shiftedSecond_right_measurable t p)))

def sourceSecondCompositionMajorant (w : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  sourceSecondCompositionBound*(frequencyDecay101 w.1*frequencyDecay101 w.2)

theorem sourceSecondCompositionMajorant_integrable :
    Integrable sourceSecondCompositionMajorant (volume.prod volume) :=
  (frequencyDecay101_integrable.mul_prod frequencyDecay101_integrable).const_mul _

theorem compositionSecondIntegrand_norm_bound (t : ℝ) (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) (unit : |t|≤1) :
    ‖compositionSecondIntegrand t z p w‖ ≤ sourceSecondCompositionMajorant w := by
  rw [sourceSecondCompositionMajorant,frequencyDecay101,frequencyDecay101,
    Real.rpow_neg (by positivity : (0 : ℝ)≤1+‖w.1‖),
    Real.rpow_neg (by positivity : (0 : ℝ)≤1+‖w.2‖)]
  rw [show (1+‖w.1‖)^(101 : ℝ)=(1+‖w.1‖)^(101 : ℕ) from Real.rpow_natCast _ _,
    show (1+‖w.2‖)^(101 : ℝ)=(1+‖w.2‖)^(101 : ℕ) from Real.rpow_natCast _ _,
    ←mul_inv,←div_eq_mul_inv,le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using compositionSecondIntegrand_101_bound t z p w unit

theorem compositionSecondIntegrand_integrable (t : ℝ) (z p : PhysicalMomentum) (unit : |t|≤1) :
    Integrable (compositionSecondIntegrand t z p) (volume.prod volume) :=
  sourceSecondCompositionMajorant_integrable.mono
    (compositionSecondIntegrand_measurable t z p).aestronglyMeasurable
    (Eventually.of_forall fun w => (compositionSecondIntegrand_norm_bound t z p w unit).trans (le_abs_self _))

end LowEnergy.PreparationVacuumJetDecay
