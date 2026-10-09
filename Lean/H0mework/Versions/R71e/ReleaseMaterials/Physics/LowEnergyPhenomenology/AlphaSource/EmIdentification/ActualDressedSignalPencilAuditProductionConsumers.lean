import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalPencil

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedSignalPencilAudit
elab "checked_dressed_window_polarization_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_window_polarization_actual).type
theorem checked_dressed_window_polarization_actual : checked_dressed_window_polarization_actualContract := @LowEnergy.GaussComposite.ActualDressedPencil.dressed_window_polarization_actual

elab "checked_dressed_native_window_pencil_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_native_window_pencil_generated).type
theorem checked_dressed_native_window_pencil_generated : checked_dressed_native_window_pencil_generatedContract := @LowEnergy.GaussComposite.ActualDressedPencil.dressed_native_window_pencil_generated

elab "checked_dressed_coincident_clock_factorContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPencil.dressed_coincident_clock_factor).type
theorem checked_dressed_coincident_clock_factor : checked_dressed_coincident_clock_factorContract := @LowEnergy.GaussComposite.ActualDressedPencil.dressed_coincident_clock_factor

open SaturationMonoid.PhysicsCore StageNineHolonomicField ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open SourcePropagationMotherEulerKernel SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal
open MeasureTheory Filter Set
open ActualDressedPencil
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] nativeHessian dressedSignalRawEuler dressedNativeWindowPencil

theorem zero_actual_input_window (p : Fin 4→ℂ) (lambda : ℂ) : dressedClassicalTimeFactor p lambda 0=0 := by
  simp only [dressedClassicalTimeFactor,intervalIntegral.integral_same]

theorem actual_coincident_clock_nonzero (p : Fin 4→ℂ) (T : ℝ) (future : 0<T) :
    dressedClassicalTimeFactor p (p 0) T≠0 := by
  rw [dressed_coincident_clock_factor]
  exact_mod_cast future.ne'

theorem shifted_clock_does_not_drop_weight : dressedClassicalTimeFactor 0 1 1≠1 := by
  have paid (t : ℝ) : HasDerivAt (fun s : ℝ=> -Complex.exp (-(s:ℂ))) (Complex.exp (-(t:ℂ))) t := by
    have base:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)
    simpa using! base.neg.cexp.neg
  have continuousIntegrand : Continuous (fun t : ℝ=>Complex.exp (-(t:ℂ))) := by fun_prop
  have original:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>paid t)
    (continuousIntegrand.intervalIntegrable (0:ℝ) 1)
  have equation : dressedClassicalTimeFactor 0 1 1=1-Complex.exp (-1) := by
    simpa [dressedClassicalTimeFactor,laplaceWeight,sub_eq_add_neg,add_comm] using original
  rw [equation]
  intro same
  have contradiction : Complex.exp (-1)=0 := by linear_combination -same
  exact Complex.exp_ne_zero _ contradiction

end LowEnergy.GaussComposite.ActualDressedSignalPencilAudit

