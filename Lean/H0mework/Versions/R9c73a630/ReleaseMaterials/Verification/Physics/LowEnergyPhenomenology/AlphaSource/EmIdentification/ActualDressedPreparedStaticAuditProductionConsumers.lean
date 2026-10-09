import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparedTimePrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparedSlopePrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparedSlopeGrowth
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFiniteStaticRead

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit
elab "checked_occupationPrice_nonnegContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_nonneg).type
theorem checked_occupationPrice_nonneg : checked_occupationPrice_nonnegContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_nonneg

elab "checked_occupationPrice_monoContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_mono).type
theorem checked_occupationPrice_mono : checked_occupationPrice_monoContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_mono

elab "checked_actual_time_N2_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_return).type
theorem checked_actual_time_N2_return : checked_actual_time_N2_returnContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_return

elab "checked_actual_time_N2_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_price).type
theorem checked_actual_time_N2_price : checked_actual_time_N2_priceContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_time_N2_price

elab "checked_actual_created_time_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_time_price).type
theorem checked_actual_created_time_price : checked_actual_created_time_priceContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_time_price

elab "checked_actual_background_time_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_background_time_price).type
theorem checked_actual_background_time_price : checked_actual_background_time_priceContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_background_time_price

elab "checked_actual_timeSlope_N2_rangeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_range).type
theorem checked_actual_timeSlope_N2_range : checked_actual_timeSlope_N2_rangeContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_range

elab "checked_actual_timeSlope_N2_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_price).type
theorem checked_actual_timeSlope_N2_price : checked_actual_timeSlope_N2_priceContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_price

elab "checked_actual_created_timeSlope_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_price).type
theorem checked_actual_created_timeSlope_price : checked_actual_created_timeSlope_priceContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_price

elab "checked_occupationPrice_twoContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two).type
theorem checked_occupationPrice_two : checked_occupationPrice_twoContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two

elab "checked_occupationPrice_two_growthContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two_growth).type
theorem checked_occupationPrice_two_growth : checked_occupationPrice_two_growthContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.occupationPrice_two_growth

elab "checked_actual_timeSlope_N2_polynomial_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_polynomial_price).type
theorem checked_actual_timeSlope_N2_polynomial_price : checked_actual_timeSlope_N2_polynomial_priceContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_timeSlope_N2_polynomial_price

elab "checked_actual_created_timeSlope_polynomial_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_polynomial_price).type
theorem checked_actual_created_timeSlope_polynomial_price : checked_actual_created_timeSlope_polynomial_priceContract := @LowEnergy.GaussComposite.ActualDressedPreparedPrice.actual_created_timeSlope_polynomial_price

elab "checked_finite_constant_field_slope_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_constant_field_slope_actual).type
theorem checked_finite_constant_field_slope_actual : checked_finite_constant_field_slope_actualContract := @LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_constant_field_slope_actual

elab "checked_finite_static_integrand_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_integrand_integrable).type
theorem checked_finite_static_integrand_integrable : checked_finite_static_integrand_integrableContract := @LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_integrand_integrable

elab "checked_dressed_static_polarization_finiteContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.dressed_static_polarization_finite).type
theorem checked_dressed_static_polarization_finite : checked_dressed_static_polarization_finiteContract := @LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.dressed_static_polarization_finite

elab "checked_finite_static_polarization_tailContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_polarization_tail).type
theorem checked_finite_static_polarization_tail : checked_finite_static_polarization_tailContract := @LowEnergy.GaussComposite.ActualDressedFiniteStaticRead.finite_static_polarization_tail

open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open PreparationVacuumNoetherChart PreparationVacuumJointFieldResponse
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedNoether ActualDressedNumberSector
open ActualDressedNumberZero GaussComposite.SourceGraph PreparationVacuumSourcePreparedResponse
open PreparationVacuumPhysicalN1WardCollapse FullYSourceCutoffVolterra
open scoped InnerProductSpace

theorem actual_event_nonempty : Nonempty DressedEvent := by
  exact ⟨{
    epsilon := 1
    precision := by norm_num
    momentum := 0
    frame := Classical.choice inferInstance
    cut := 0
    energy := Complex.I
    nonreal := by simp
  }⟩

theorem actual_unit_nonzero (event : DressedEvent) : sourceDressedUnit event.epsilon event.precision≠0 := by
  intro zero
  have norm:=source_dressed_unit_norm event.epsilon event.precision
  rw [zero,norm_zero] at norm
  exact zero_ne_one norm


open ActualDressedFieldTime Filter
open scoped Topology



open ActualDressedPreparedPrice ActualDressedFiniteStaticRead MeasureTheory
open scoped Interval

theorem same_actual_created_slope_price (event : DressedEvent) (force : Field289) (t : ℝ) :
    ‖timeSlope force event.momentum event.frame t (sourceDressedUnit event.epsilon event.precision)‖ ≤
      (‖jointCurrent event.momentum event.frame 0 0 force‖*(1+‖actualA event.momentum event.frame‖)^4)*(1+|t|)^5 :=
  actual_created_timeSlope_polynomial_price event.momentum event.frame force event.epsilon event.precision t

theorem same_actual_finite_static_entry (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0<lambda.re) (i j : Fin 289) :
    ActualDressedSylvester.dressedStaticPolarization event transfer lambda i j=
      ∫t in Set.Ioi (0:ℝ),PreparationVacuumGaugeSourceInjection.laplaceWeight lambda t*
        finiteConstantFieldSlope event transfer (PreparationVacuumActionFieldLift.fieldUnit j) t i :=
  dressed_static_polarization_finite event transfer lambda positive i j

theorem same_actual_finite_static_tail (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (static : p 0=0) (lambda : ℂ) (positive : 0<lambda.re)
    (T : ℝ) (future : 0≤T) (i j : Fin 289) :
    ‖(∫t in Set.Ioi (0:ℝ),PreparationVacuumGaugeSourceInjection.laplaceWeight lambda t*
        finiteConstantFieldSlope event transfer (PreparationVacuumActionFieldLift.fieldUnit j) t i)-
      ActualDressedPencil.dressedWindowPolarization event transfer p lambda T i j‖ ≤
        ActualDressedSignal.dressedSignalTailPrice event transfer p lambda T :=
  finite_static_polarization_tail event transfer p static lambda positive T future i j
end LowEnergy.GaussComposite.ActualDressedPreparedStaticAudit

