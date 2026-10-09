import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualNullNativeTable
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualNullNativeColumn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedConstraintTranspose
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedConstraintHistory

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedConstraintWardAudit
elab "checked_original_null_column_literalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_column_literal).type
theorem checked_original_null_column_literal : checked_original_null_column_literalContract := @LowEnergy.GaussComposite.ActualDressedNullNative.original_null_column_literal

elab "checked_original_null_cokernelContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_cokernel).type
theorem checked_original_null_cokernel : checked_original_null_cokernelContract := @LowEnergy.GaussComposite.ActualDressedNullNative.original_null_cokernel

elab "checked_original_null_lift_singleContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_lift_single).type
theorem checked_original_null_lift_single : checked_original_null_lift_singleContract := @LowEnergy.GaussComposite.ActualDressedNullNative.original_null_lift_single

elab "checked_source_cokernel_actual_pencilContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_cokernel_actual_pencil).type
theorem checked_source_cokernel_actual_pencil : checked_source_cokernel_actual_pencilContract := @LowEnergy.GaussComposite.ActualDressedConstraintWard.source_cokernel_actual_pencil

elab "checked_dressed_complex_reader_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_complex_reader_actual).type
theorem checked_dressed_complex_reader_actual : checked_dressed_complex_reader_actualContract := @LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_complex_reader_actual

elab "checked_dressed_quantum_reader_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_quantum_reader_actual).type
theorem checked_dressed_quantum_reader_actual : checked_dressed_quantum_reader_actualContract := @LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_quantum_reader_actual

elab "checked_source_constraint_quantum_historyContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_quantum_history).type
theorem checked_source_constraint_quantum_history : checked_source_constraint_quantum_historyContract := @LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_quantum_history

elab "checked_source_constraint_nonlinear_historyContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_nonlinear_history).type
theorem checked_source_constraint_nonlinear_history : checked_source_constraint_nonlinear_historyContract := @LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_nonlinear_history

elab "checked_source_constraint_schur_historyContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_schur_history).type
theorem checked_source_constraint_schur_history : checked_source_constraint_schur_historyContract := @LowEnergy.GaussComposite.ActualDressedConstraintWard.source_constraint_schur_history

open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumOriginalGreenFeedback
open ActualEMDressedSchur ActualDressedNullNative
open scoped Matrix BigOperators

theorem checked_parent_original_lift (p : Fin 4→ℂ) (n : Fin 9) :
    sourceNullLift p (Pi.single n 1)=originalNullColumn p n := original_null_lift_single p n

theorem checked_parent_column_temporal_sign (p : Fin 4→ℂ) : originalNullColumn p 0 10= -(p 0)/2 := by
  rw [original_null_column_literal]
  norm_num [nullColumnTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    nullColumnIndex,Fin.ext_iff,Powers.value,coefficientValue]
  ring

theorem checked_parent_opposite_cokernel_sign (p : Fin 4→ℂ) : sourceCokernel p (Pi.single 10 1) 0=p 0/2 := by
  rw [original_null_cokernel]
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [original_null_column_literal]
  norm_num [nullColumnTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    nullColumnIndex,Fin.ext_iff,Powers.value,coefficientValue]
  ring

theorem checked_parent_other_column_zero (p : Fin 4→ℂ) : sourceCokernel p (Pi.single 10 1) 1=0 := by
  rw [original_null_cokernel]
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [original_null_column_literal]
  norm_num [nullColumnTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    nullColumnIndex,Fin.ext_iff]


open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalVoltageCompleteReturn
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open SourcePropagationNativeActionHessian SourcePropagationNoetherTime SourcePropagationMotherEulerKernel
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse ActualEMDressedConstraint ActualEMDressedSchur
open ActualDressedConstraintRead ActualDressedNullNative ActualDressedConstraintWard
open MeasureTheory
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] originalChange dressedEulerObserver noetherHistoryOperatorJet dressedNoetherJet

/-- The original derivative column detects the opposite Fourier momentum. -/
theorem original_opposite_momentum_detected :
    originalNullColumn (-(Pi.single 0 1 : Fin 4→ℂ)) 0 10≠
      originalNullColumn (Pi.single 0 1) 0 10 := by
  rw [original_null_column_literal,original_null_column_literal]
  norm_num [nullColumnTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    nullColumnIndex,Fin.ext_iff,Powers.value,coefficientValue,Pi.single_apply]

/-- A pure imaginary reader remains an actual real source field multiplied once by I. -/
theorem actual_imaginary_reader (event : DressedEvent) (transfer : PhysicalMomentum)
    (f : Field289) (signal : ℝ→SourceJet Field289) (t : ℝ) :
    dressedComplexReader event transfer (fun j=>Complex.I*(f j:ℂ)) signal t=
      Complex.I*dressedEulerObserver event
        (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) f signal t).value := by
  rw [dressed_complex_reader_actual,actual_noether_reader_contraction,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Even at zero quantum age, the full Schur forcing has its original nine-row responsibility. -/
theorem actual_zero_age_forcing (event : DressedEvent) (forcing : SignalAmplitude)
    (initial : Fin 9→ℂ) (n : Fin 9) :
    (anchorSchur event 0*ᵥinitial-anchorSchurSource event 0 forcing) n=sourceCokernel anchorInput forcing n := by
  rw [source_constraint_schur_history]
  simp

end LowEnergy.GaussComposite.ActualDressedConstraintWardAudit

