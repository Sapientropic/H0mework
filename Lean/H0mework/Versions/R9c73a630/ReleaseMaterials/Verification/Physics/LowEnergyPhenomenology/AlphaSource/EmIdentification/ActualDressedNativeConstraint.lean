import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualNullNativeRead
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedConstraintHistory

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNativeConstraint
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction PreparationVacuumNoetherChart
open PreparationVacuumOriginalDensity PreparationVacuumSourceActionJets PreparationVacuumFullFieldRiesz
open PreparationVacuumNonlinearFieldCurve PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback GaussQuantumMultiplier
open SourcePropagationNativeActionHessian SourcePropagationNoetherTime SourcePropagationNativeEulerHistory
open SourcePropagationTimeDependentFeedback SourcePropagationMotherEulerKernel
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse ActualEMDressedConstraint ActualEMDressedSchur
open ActualDressedConstraintWard ActualDressedNullNative ActualDressedLockedWard
open MeasureTheory
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] dressedEulerObserver noetherHistoryOperatorJet nativeReader nativeReaderContact
  originalNullColumn originalNullReal nativeSourceColumn nativeWardHistory jointResolvent physicalTime jointCurrent

private theorem zero_reference_deviation (n : Fin 9) (s : ActionState) : nativeReferenceDeviation n 0 s=0 :=by
  simp [nativeReferenceDeviation,stateContact]
  rfl

private theorem zero_noether_deviation (n : Fin 9) (p : PhysicalMomentum) (base candidate : ActionState) :
    nativeDeviationNoether n 0 p base candidate=0 :=by
  simp only [nativeDeviationNoether,zero_reference_deviation,symbolFirst,map_zero,mul_zero,smul_zero]

/-- The imaginary parameter value is zero; its configuration deviation vanishes before taking any quantum expectation. -/
theorem native_zero_deviation_reader (n : Fin 9) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    nativeDeviationReader n 0 p F=0 :=by
  funext h
  simp [nativeDeviationReader,finiteRiesz,nativeDeviationForm,nativeDeviationSample,
    zero_noether_deviation,pairSample]

theorem native_zero_deviation_contact (n : Fin 9) (force : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) : nativeDeviationReaderContact n 0 force p F=0 :=by
  rw [nativeDeviationReaderContact,native_zero_deviation_reader]
  simp

private def symmetryHistory (event : DressedEvent) (transfer : PhysicalMomentum) (n : Fin 9)
    (theta : ℝ) (gradient : Fin 4→ℝ) (signal : ℝ→SourceJet Field289) (t : ℝ) : ℂ:=
  dressedEulerObserver event
    (nativeWardHistory (dressedKinematicPoint event transfer)
      (nativeReader n theta gradient event.momentum event.frame 0)
      (fun force=>nativeReaderContact n theta gradient force event.momentum event.frame)
      (fun s=>(signal s).value) t)

private def deviationHistory (event : DressedEvent) (transfer : PhysicalMomentum) (n : Fin 9)
    (theta : ℝ) (signal : ℝ→SourceJet Field289) (t : ℝ) : ℂ:=
  dressedEulerObserver event
    (nativeWardHistory (dressedKinematicPoint event transfer)
      (nativeDeviationReader n theta event.momentum event.frame 0)
      (fun force=>nativeDeviationReaderContact n theta force event.momentum event.frame)
      (fun s=>(signal s).value) t)

private theorem zero_deviation_history (event : DressedEvent) (transfer : PhysicalMomentum) (n : Fin 9)
    (signal : ℝ→SourceJet Field289) (t : ℝ) : deviationHistory event transfer n 0 signal t=0 :=by
  simp only [deviationHistory,native_zero_deviation_reader,Pi.zero_apply,native_zero_deviation_contact,
    nativeWardHistory,mul_zero,zero_mul,add_zero,map_zero]

private theorem complex_reader_native (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (n : Fin 9) (signal : ℝ→SourceJet Field289) (t : ℝ) :
    dressedComplexReader event transfer (originalNullColumn (-p) n) signal t=
      symmetryHistory event transfer n 1 (fun mu=>((-p) mu).re) signal t+
      Complex.I*symmetryHistory event transfer n 0 (fun mu=>((-p) mu).im) signal t-
      deviationHistory event transfer n 1 signal t :=by
  have realRead : dressedEulerObserver event
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer)
        (fun row=>(originalNullColumn (-p) n row).re) signal t).value=
      symmetryHistory event transfer n 1 (fun mu=>((-p) mu).re) signal t-
        deviationHistory event transfer n 1 signal t :=by
    have same:=congrArg (fun f : Field289=>dressedEulerObserver event
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) f signal t).value)
      (original_null_real_part (-p) n)
    exact same.trans (original_null_actual_history event transfer n (fun mu=>((-p) mu).re) signal t)
  have imaginaryRead : dressedEulerObserver event
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer)
        (fun row=>(originalNullColumn (-p) n row).im) signal t).value=
      symmetryHistory event transfer n 0 (fun mu=>((-p) mu).im) signal t :=by
    have same:=congrArg (dressedEulerObserver event)
      (original_null_imaginary_history (dressedKinematicPoint event transfer) (-p) n signal t)
    have actual:=native_reference_actual_history event transfer n 0 (fun mu=>((-p) mu).im) signal t
    change _=symmetryHistory event transfer n 0 (fun mu=>((-p) mu).im) signal t-
      deviationHistory event transfer n 0 signal t at actual
    rw [zero_deviation_history,sub_zero] at actual
    exact same.trans actual
  change dressedEulerObserver event
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer)
        (fun row=>(originalNullColumn (-p) n row).re) signal t).value+
    Complex.I*dressedEulerObserver event
      (noetherHistoryOperatorJet (dressedKinematicPoint event transfer)
        (fun row=>(originalNullColumn (-p) n row).im) signal t).value=_
  rw [realRead,imaginaryRead]
  ring

/-- Four original real quadratures, with the opposite-momentum reader parameters generated from the original null columns. -/
def nativeConstraintHistory (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (n : Fin 9) (a : SignalAmplitude) (t : ℝ) : ℂ:=
  symmetryHistory event transfer n 1 (fun mu=>((-p) mu).re) (nativeTimeSignal (sourceRealSignal p a)) t+
  Complex.I*symmetryHistory event transfer n 0 (fun mu=>((-p) mu).im) (nativeTimeSignal (sourceRealSignal p a)) t+
  Complex.I*symmetryHistory event transfer n 1 (fun mu=>((-p) mu).re)
    (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) t-
  symmetryHistory event transfer n 0 (fun mu=>((-p) mu).im)
    (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) t

/-- Both real-input histories retain their actual configuration/reference deviation. -/
def nativeConstraintDeviation (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (n : Fin 9) (a : SignalAmplitude) (t : ℝ) : ℂ:=
  deviationHistory event transfer n 1 (nativeTimeSignal (sourceRealSignal p a)) t+
  Complex.I*deviationHistory event transfer n 1 (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) t

theorem native_constraint_quadratures (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (n : Fin 9) (a : SignalAmplitude) (t : ℝ) :
    dressedQuantumReader event transfer (originalNullColumn (-p) n) p a t=
      nativeConstraintHistory event transfer p n a t-nativeConstraintDeviation event transfer p n a t :=by
  rw [dressedQuantumReader,complex_reader_native,complex_reader_native]
  simp only [nativeConstraintHistory,nativeConstraintDeviation]
  linear_combination Complex.I_sq*symmetryHistory event transfer n 0 (fun mu=>((-p) mu).im)
    (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) t

/-- All289 original source coefficients enter the same C9 quantum response; only the proven Noether restriction is consumed. -/
theorem source_constraint_native_history (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (lambda : ℂ) (T : ℝ) (a : SignalAmplitude) (n : Fin 9) :
    sourceCokernel p (dressedWindowPolarization event transfer p lambda T*ᵥa) n=
      ∫t in (0:ℝ)..T,laplaceWeight lambda t*
        (nativeConstraintHistory event transfer p n a t-nativeConstraintDeviation event transfer p n a t) :=by
  rw [source_constraint_quantum_history]
  simp_rw [native_constraint_quadratures]

/-- The original actual nonlinear window produces these same native Ward and reference-deviation histories. -/
theorem source_constraint_native_nonlinear (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (lambda : ℂ) (T : ℝ) (future : 0 ≤ T) (a : SignalAmplitude)
    (inside : T<dressedSignalDuration event transfer p a) (n : Fin 9) :
    sourceCokernel p
      (fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*deriv (fun r=>dressedSignalRawEuler event transfer p a r t i) 0) n=
      -(∫t in (0:ℝ)..T,laplaceWeight lambda t*
        (nativeConstraintHistory event transfer p n a t-nativeConstraintDeviation event transfer p n a t)) :=by
  rw [source_constraint_nonlinear_history event transfer p lambda T future a inside]
  simp_rw [native_constraint_quadratures]

/-- The retained nine initial coordinates and the original source forcing consume the same generated quantum Ward return. -/
theorem source_constraint_native_schur (event : DressedEvent) (T : ℝ) (forcing : SignalAmplitude)
    (initial : Fin 9→ℂ) (n : Fin 9) :
    (anchorSchur event T*ᵥinitial-anchorSchurSource event T forcing) n=
      sourceCokernel anchorInput forcing n+
        ∫t in (0:ℝ)..T,laplaceWeight 3 t*
          (nativeConstraintHistory (anchorEvent event) 0 anchorInput n
            (anchorResponseNine event T forcing initial) t-
           nativeConstraintDeviation (anchorEvent event) 0 anchorInput n
            (anchorResponseNine event T forcing initial) t) :=by
  rw [source_constraint_schur_history]
  simp_rw [native_constraint_quadratures]

end LowEnergy.GaussComposite.ActualDressedNativeConstraint
