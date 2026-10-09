import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedConstraintClockColumns
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFullSchurFlux

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFullSchurFluxAudit
elab "checked_clock_native_columns_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_actual).type
theorem checked_clock_native_columns_actual : checked_clock_native_columns_actualContract := @LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_actual

elab "checked_clock_native_columns_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_derivative).type
theorem checked_clock_native_columns_derivative : checked_clock_native_columns_derivativeContract := @LowEnergy.GaussComposite.ActualDressedSchurClock.clock_native_columns_derivative

elab "checked_clock_schur_original_productContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_schur_original_product).type
theorem checked_clock_schur_original_product : checked_clock_schur_original_productContract := @LowEnergy.GaussComposite.ActualDressedSchurClock.clock_schur_original_product

elab "checked_clock_source_schur_flux_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSchurClock.clock_source_schur_flux_generated).type
theorem checked_clock_source_schur_flux_generated : checked_clock_source_schur_flux_generatedContract := @LowEnergy.GaussComposite.ActualDressedSchurClock.clock_source_schur_flux_generated

open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalVoltageCompleteReturn
open PreparationVacuumCurrentSignalOperator
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedClockMoment ActualDressedPhysicalClock
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse ActualEMDressedConstraint ActualEMDressedSchur
open ActualDressedNullNative ActualEMDressedClockGerm ActualEMDressedClockSchur ActualDressedSchurClock
open Filter
open scoped Matrix BigOperators Topology
attribute [local irreducible] originalChange clockSchur clockSourceSchurFlux dressedWindowPolarization

/-- Both genuine constraint maps have nonzero original clock derivatives. -/
theorem actual_source_column_jets :
    clockNativeNullJet 10 0=-(1/2:ℂ) ∧ (-clockNativeNullJet.transpose) 0 10=(1/2:ℂ) := by
  have right : clockNativeNullJet 10 0=-(1/2:ℂ) := by
    change originalNullColumn (sourceInputClock 1) 0 10-originalNullColumn (sourceInputClock 0) 0 10=-(1/2:ℂ)
    rw [original_null_column_literal,original_null_column_literal]
    norm_num [nullColumnTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
      nullColumnIndex,Fin.ext_iff,Powers.value,coefficientValue,sourceInputClock,Pi.single_apply]
  refine ⟨right,?_⟩
  rw [Matrix.neg_apply,Matrix.transpose_apply,right]
  norm_num

/-- The germ is consumed at a source-generated nonlinear window for an actual nonzero field amplitude. -/
theorem actual_anchor_schur_flux (event : DressedEvent) :
    HasDerivAt (clockSchur event (anchorWindow event (Pi.single 20 1)))
      (clockSourceSchurFlux event (anchorWindow event (Pi.single 20 1)) 3) 3 := by
  have window:=anchor_window_source event (Pi.single 20 1)
  exact (clock_source_schur_flux_generated event _ window.1 window.2.1).self_of_nhds

/-- Real frequency on the nonempty original damped germ carries exactly one minus-I. -/
theorem actual_damped_frequency_factor (event : DressedEvent) :
    HasDerivAt (fun w : ℝ=>clockSchur event (anchorWindow event (Pi.single 20 1)) (3-Complex.I*(w:ℂ)))
      ((-Complex.I) • clockSourceSchurFlux event (anchorWindow event (Pi.single 20 1)) 3) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have entry : HasDerivAt (fun z=>clockSchur event (anchorWindow event (Pi.single 20 1)) z i j)
      (clockSourceSchurFlux event (anchorWindow event (Pi.single 20 1)) 3 i j) ((3:ℂ)-Complex.I*0) := by
    simpa using! hasDerivAt_pi.mp (hasDerivAt_pi.mp (actual_anchor_schur_flux event) i) j
  have path : HasDerivAt (fun w : ℂ=>3-Complex.I*w) (-Complex.I) 0 := by
    simpa only [zero_sub,mul_one] using! (hasDerivAt_const (0:ℂ) (3:ℂ)).sub
      ((hasDerivAt_id (0:ℂ)).const_mul Complex.I)
  have mapped:=entry.comp (0:ℂ) path
  simpa only [Function.comp_def,Matrix.smul_apply,smul_eq_mul,mul_comm (-Complex.I)] using! mapped.comp_ofReal

end LowEnergy.GaussComposite.ActualDressedFullSchurFluxAudit

