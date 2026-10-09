import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativeFourierHistory

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentSignalRealization
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open SourcePropagationNativeActionHessian SourcePropagationNativeEulerHistory SourcePropagationMotherEulerKernel
open SourcePropagationMotherResidualDirections SourcePropagationNoetherTime SourcePropagationTimeDependentFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumOriginalGreenFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumFieldConstraintResponse
open Filter MeasureTheory
open scoped BigOperators ContDiff Topology Matrix Interval
attribute [local irreducible] nativeHessian nativeJetDensity nativeConfiguration nativeJetBasis
  actualPreparedRawMotherEuler actualPreparedHistorySource originalJacobi originalReader36 sourceCompatibility

def sourceSignalDuration (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (a : Fin 289→ℂ) : ℝ:=
  min (preparedHistoryDuration q (nativeTimeHistory (sourceRealSignal p a))
    (motherHistoryRegular _ (sourceRealSignal_smooth p a)))
    (preparedHistoryDuration q (nativeTimeHistory (sourceRealSignal p (sourceQuadrature a)))
      (motherHistoryRegular _ (sourceRealSignal_smooth p (sourceQuadrature a))))

theorem sourceSignalDuration_positive (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (a : Fin 289→ℂ) :
    0<sourceSignalDuration q p a :=by
  exact lt_min (preparedHistoryDuration_positive _ _ _) (preparedHistoryDuration_positive _ _ _)

def sourceSignalCurrent (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (a : Fin 289→ℂ)
    (t : ℝ) (i : Fin 289) : ℂ:=
  (noetherHistorySourceJet q (nativeTimeSignal (sourceRealSignal p a)) t i).value+
    Complex.I*(noetherHistorySourceJet q (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) t i).value

theorem sourceRawSignalEuler_generated (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (a : Fin 289→ℂ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) (nonnegative : 0≤t)
    (inside : t<sourceSignalDuration q p a) (i : Fin 289) :
    HasDerivAt (fun r : ℝ=>actualPreparedRawMotherEuler q (sourceRealSignal p a)
      (sourceRealSignal_smooth p a) r t i)
      (Complex.ofReal ((nativeFourierHessian nativeHessian p*ᵥ
        sourceSignalAmplitude p a (nativeTimePoint t)) i).re-
          (noetherHistorySourceJet q (nativeTimeSignal (sourceRealSignal p a)) t i).value) 0 :=by
  have source:=actualPreparedRawMotherEuler_generated q (sourceRealSignal p a) (sourceRealSignal_smooth p a)
    hz hw t nonnegative ((lt_min_iff.mp inside).1) i
  rwa [sourceRealSignal_secondJet,sourceRealEuler_Fourier] at source

/-- The quantum term is produced separately by the same two real nonlinear source families, preserving its full spectral and current dependence. -/
theorem sourcePreparedQuadrature_generated (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (a : Fin 289→ℂ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) (nonnegative : 0≤t)
    (inside : t<sourceSignalDuration q p a) (i : Fin 289) :
    HasDerivAt (fun r : ℝ=>
      actualPreparedRawMotherEuler q (sourceRealSignal p a) (sourceRealSignal_smooth p a) r t i+
      Complex.I*actualPreparedRawMotherEuler q (sourceRealSignal p (sourceQuadrature a))
        (sourceRealSignal_smooth p (sourceQuadrature a)) r t i)
      ((nativeFourierHessian nativeHessian p*ᵥsourceSignalAmplitude p a (nativeTimePoint t)) i-
        sourceSignalCurrent q p a t i) 0 :=by
  have left:=actualPreparedRawMotherEuler_generated q (sourceRealSignal p a) (sourceRealSignal_smooth p a)
    hz hw t nonnegative ((lt_min_iff.mp inside).1) i
  have right:=actualPreparedRawMotherEuler_generated q (sourceRealSignal p (sourceQuadrature a))
    (sourceRealSignal_smooth p (sourceQuadrature a)) hz hw t nonnegative ((lt_min_iff.mp inside).2) i
  have generated:=left.add (right.const_mul Complex.I)
  apply generated.congr_deriv
  rw [sourceSignalCurrent,←sourceEuler_quadrature p a (nativeTimePoint t) i]
  ring

theorem sourceSignalCurrent_actual (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (a : Fin 289→ℂ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) (nonnegative : 0≤t)
    (inside : t<sourceSignalDuration q p a) (i : Fin 289) :
    sourceSignalCurrent q p a t i=
      actualHistoryLinearSource q (nativeTimeSignal (sourceRealSignal p a))
        (motherHistoryRegular _ (sourceRealSignal_smooth p a)) t i+
      Complex.I*actualHistoryLinearSource q (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a)))
        (motherHistoryRegular _ (sourceRealSignal_smooth p (sourceQuadrature a))) t i :=by
  rw [sourceSignalCurrent,
    ←actualHistoryLinearSource_value q _ _ hz hw t nonnegative ((lt_min_iff.mp inside).1),
    ←actualHistoryLinearSource_value q _ _ hz hw t nonnegative ((lt_min_iff.mp inside).2)]

theorem sourceSignalOrdinaryRemainder_generated (p : Fin 4→ℂ) (a : Fin 289→ℂ) (t : ℝ) (i : Fin 289) :
    HasDerivAt (deriv (fun r : ℝ=>actualMotherEulerRead
      (fun point=>r • sourceRealSignal p a point) (nativeTimePoint t) (Pi.single i 1)))
      (2*nativeOrdinaryRemainder (sourceRealSignal p a) t i) 0 :=
  rawMotherOrdinaryRemainder_generated _ (sourceRealSignal_smooth p a) t i

def sourceSignalForcing (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (a : Fin 289→ℂ)
    (lambda : ℂ) (T : ℝ) : Fin 289→ℂ:=
  preparedOrdinaryForcing q (sourceRealSignal p a) lambda T+
    Complex.I • preparedOrdinaryForcing q (sourceRealSignal p (sourceQuadrature a)) lambda T

def sourceSignalField (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (a : Fin 289→ℂ)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (physicalSpatial q.k) lambda.val,lambda.property⟩ (sourceSignalForcing q p a lambda.val T)

theorem sourceSignalForcing_actual (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (a : Fin 289→ℂ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (lambda : ℂ) (T : ℝ) (nonnegative : 0≤T)
    (inside : T<sourceSignalDuration q p a) :
    sourceSignalForcing q p a lambda T=
      (actualHistoryForcing q (nativeTimeSignal (sourceRealSignal p a))
        (motherHistoryRegular _ (sourceRealSignal_smooth p a)) lambda T-
          nativeRemainderForcing (sourceRealSignal p a) lambda T)+
      Complex.I • (actualHistoryForcing q (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a)))
        (motherHistoryRegular _ (sourceRealSignal_smooth p (sourceQuadrature a))) lambda T-
          nativeRemainderForcing (sourceRealSignal p (sourceQuadrature a)) lambda T) :=by
  rw [sourceSignalForcing,
    preparedOrdinaryForcing_actual q _ (sourceRealSignal_smooth p a) hz hw lambda T nonnegative ((lt_min_iff.mp inside).1),
    preparedOrdinaryForcing_actual q _ (sourceRealSignal_smooth p (sourceQuadrature a)) hz hw lambda T nonnegative ((lt_min_iff.mp inside).2)]

theorem sourceSignalField_native (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (a : Fin 289→ℂ)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) :
    nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
      sourceSignalField q p a lambda T=
        sourceSignalForcing q p a lambda.val T-
          originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
            sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val) (sourceSignalForcing q p a lambda.val T) :=by
  exact nativeAction_sourceField ⟨_,lambda.property⟩ _

theorem sourceSignalField_native36 (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (a : Fin 289→ℂ)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) :
    originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
      (nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
        sourceSignalField q p a lambda T)=
      originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥsourceSignalForcing q p a lambda.val T-
        originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
          (originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
            sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val) (sourceSignalForcing q p a lambda.val T)) :=by
  rw [sourceSignalField_native,Matrix.mulVec_sub]

theorem sourceSignalForcing_cosources (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (a : Fin 289→ℂ)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) (row : Fin 289) :
    (originalReadback (fullMomentum spatial lambda)*ᵥsourceSignalForcing q p a lambda T) row=
      ((∫t in (0 : ℝ)..T,laplaceWeight lambda t*preparedOrdinaryTimeSource q (sourceRealSignal p a) spatial t row)-
        (preparedOrdinaryBoundary q (sourceRealSignal p a) spatial lambda T row-
          preparedOrdinaryBoundary q (sourceRealSignal p a) spatial lambda 0 row))+
      Complex.I*((∫t in (0 : ℝ)..T,laplaceWeight lambda t*
          preparedOrdinaryTimeSource q (sourceRealSignal p (sourceQuadrature a)) spatial t row)-
        (preparedOrdinaryBoundary q (sourceRealSignal p (sourceQuadrature a)) spatial lambda T row-
          preparedOrdinaryBoundary q (sourceRealSignal p (sourceQuadrature a)) spatial lambda 0 row)) :=by
  rw [sourceSignalForcing,Matrix.mulVec_add,Matrix.mulVec_smul]
  change _+Complex.I*_= _
  rw [preparedOrdinaryForcing_cosources q _ (sourceRealSignal_smooth p a),
    preparedOrdinaryForcing_cosources q _ (sourceRealSignal_smooth p (sourceQuadrature a))]

end LowEnergy.PreparationVacuumCurrentSignalRealization
