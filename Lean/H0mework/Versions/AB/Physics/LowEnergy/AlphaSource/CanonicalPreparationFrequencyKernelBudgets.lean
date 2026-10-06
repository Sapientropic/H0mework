import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationFrequencyConvolutionMajorant

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFrequencyN2
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumFourierJets
open PreparationVacuumMomentumFirst PreparationVacuumTaylor PreparationVacuumRemainder
open PreparationVacuumJetDecay PreparationVacuumGlobalN2 PreparationVacuumCompositionReadback
open CanonicalPreparationSquareCutoff CanonicalPreparationCutoff MeasureTheory Filter Set
open scoped ContDiff Topology SchwartzMap FourierTransform RealInnerProductSpace BigOperators
attribute [local irreducible] partialFourier symbolSlice actualFullCompositionKernelDefect

theorem compositionFrequency_joint_measurable (t : ℝ) :
    StronglyMeasurable (fun w : PhysicalMomentum × PhysicalMomentum => compositionFrequency t w.1 w.2) := by
  have left : Continuous (fun w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum =>
      (w.1.1+(t*Real.pi) • (w.1.2-w.2),w.2)) :=
    ((continuous_fst.comp continuous_fst).add
      (((continuous_snd.comp continuous_fst).sub continuous_snd).const_smul (t*Real.pi))).prodMk continuous_snd
  have right : Continuous (fun w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum =>
      (w.1.1-(t*Real.pi) • w.2,w.1.2-w.2)) :=
    ((continuous_fst.comp continuous_fst).sub
      (continuous_snd.const_smul (t*Real.pi))).prodMk
      ((continuous_snd.comp continuous_fst).sub continuous_snd)
  have whole : StronglyMeasurable
      (fun w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum =>
        frequencyProductIntegrand t w.1.1 (w.2,w.1.2)) :=
    (partialFourier_joint_measurable.comp_measurable left.measurable).mul
      (partialFourier_joint_measurable.comp_measurable right.measurable)
  exact whole.integral_prod_right' (ν := (volume : Measure PhysicalMomentum))

theorem sourceFrequencyDefect_joint_measurable :
    StronglyMeasurable (fun w : PhysicalMomentum × PhysicalMomentum => sourceFrequencyDefect w.1 w.2) :=
  (compositionFrequency_joint_measurable 1).sub (compositionFrequency_joint_measurable 0)

theorem actualFullCompositionKernelDefect_measurable :
    StronglyMeasurable (fun w : PhysicalMomentum × PhysicalMomentum => actualFullCompositionKernelDefect w.1 w.2) := by
  have physical : Continuous (fun w : PhysicalMomentum × PhysicalMomentum =>
      (physicalMidpoint w.1 w.2,w.1-w.2)) :=
    ((continuous_fst.add continuous_snd).const_smul Real.pi).prodMk (continuous_fst.sub continuous_snd)
  have actual := sourceFrequencyDefect_joint_measurable.comp_measurable physical.measurable
  have same : (fun w : PhysicalMomentum × PhysicalMomentum => actualFullCompositionKernelDefect w.1 w.2)=
      (fun w => sourceFrequencyDefect (physicalMidpoint w.1 w.2) (w.1-w.2)) :=
    funext fun w => actualFullCompositionKernelDefect_sourceFrequency w.1 w.2
  rw [same]
  exact actual

theorem actualKernel_row_integrable (xi : PhysicalMomentum) :
    Integrable (fun eta : PhysicalMomentum => actualFullCompositionKernelDefect xi eta) := by
  have actual : StronglyMeasurable (fun eta : PhysicalMomentum => actualFullCompositionKernelDefect xi eta) :=
    actualFullCompositionKernelDefect_measurable.comp_measurable (g := fun eta => (xi,eta))
      (measurable_const.prodMk measurable_id)
  apply (sourceKernelMajorant_integrable.comp_sub_left xi).mono actual.aestronglyMeasurable
  exact Eventually.of_forall fun eta =>
    (actualFullCompositionKernelDefect_norm_bound xi eta).trans (le_abs_self _)

theorem actualKernel_column_integrable (eta : PhysicalMomentum) :
    Integrable (fun xi : PhysicalMomentum => actualFullCompositionKernelDefect xi eta) := by
  have actual : StronglyMeasurable (fun xi : PhysicalMomentum => actualFullCompositionKernelDefect xi eta) :=
    actualFullCompositionKernelDefect_measurable.comp_measurable (g := fun xi => (xi,eta))
      (measurable_id.prodMk measurable_const)
  apply (sourceKernelMajorant_integrable.comp_sub_right eta).mono actual.aestronglyMeasurable
  exact Eventually.of_forall fun xi =>
    (actualFullCompositionKernelDefect_norm_bound xi eta).trans (le_abs_self _)

theorem actualKernel_row_bound (xi : PhysicalMomentum) :
    (∫ eta : PhysicalMomentum,‖actualFullCompositionKernelDefect xi eta‖) ≤ sourceCompositionSchurBound := by
  calc
    _ ≤ ∫ eta : PhysicalMomentum,sourceKernelMajorant (xi-eta) :=
      integral_mono (actualKernel_row_integrable xi).norm
        (sourceKernelMajorant_integrable.comp_sub_left xi) (actualFullCompositionKernelDefect_norm_bound xi)
    _ = ∫ k : PhysicalMomentum,sourceKernelMajorant k := integral_sub_left_eq_self _ volume xi
    _ = _ := sourceKernelMajorant_integral

theorem actualKernel_column_bound (eta : PhysicalMomentum) :
    (∫ xi : PhysicalMomentum,‖actualFullCompositionKernelDefect xi eta‖) ≤ sourceCompositionSchurBound := by
  calc
    _ ≤ ∫ xi : PhysicalMomentum,sourceKernelMajorant (xi-eta) :=
      integral_mono (actualKernel_column_integrable eta).norm
        (sourceKernelMajorant_integrable.comp_sub_right eta)
        (fun xi => actualFullCompositionKernelDefect_norm_bound xi eta)
    _ = ∫ k : PhysicalMomentum,sourceKernelMajorant k := integral_sub_right_eq_self _ eta
    _ = _ := sourceKernelMajorant_integral

end LowEnergy.PreparationVacuumFrequencyN2
