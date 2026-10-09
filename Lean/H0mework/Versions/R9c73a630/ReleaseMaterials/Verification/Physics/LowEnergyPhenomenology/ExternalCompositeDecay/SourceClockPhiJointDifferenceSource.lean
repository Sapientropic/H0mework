import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeJointForceInputPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiInputForceJointCancellation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentJointDifference
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourcePhysicalKineticSquare
open SourceClockPhiNormalizedScalarBudget SourceClockPhiRadiusSourceCurrent SourceClockPhiCombinedScalePressure
open SourceScalarEssentialBudget SourceScalarShiftedBulk SourceScalarDoubleCurrent
open FirstCurrentClockPrimitive FirstCurrentClockPrimitiveSquare BalancedInputPrimitivePayment
open ScalarBalancedPrimitive ReverseScalarGaugeWard ReverseBalancedForcePayer BalancedPrimitivePayer PrimitiveInputPayer
open FirstCurrentWholeCarrier FirstCurrentAdmissibleElectric FirstCurrentJointBudget ReverseForcePhysicalPayment
open ReverseNativeClock ReverseNativeFrequencyWard FirstCurrentGeometricPayer OriginalRCommutatorSource
open ClockPhiHeatCorrectedCovarianceSource SourceLocalizedInverseFormPayment SourceResolventBandLimit
open ScalarInputJointNoether PhaseCompressionCancellation FirstCurrentJointForceLoss MeasureTheory Filter
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev B:End:=scalarBulkComplete
private abbrev X:End:=weightedElectricCurrent
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction scalarBulkComplete balancedCompressionForce positivePrimitive
  wholeClockState wholeSourceNext correctedCompleteCore clockSourcePair originalNormalizerPrice
  normalizedState normalizedForcing scalarEnergy wholeStep reverseScalarReserve reverseNoetherFactor reverseNoetherNormCost
  wholeClockWardKernel balancedWholeForceNativeDebit clearedNativePrice compensatedPrimitiveWork
  wholeSourceMap balancedInputVector frequencyState weightedElectricCurrent completeBalancedInput balancedWholeForceState
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem frequency_gap(half:Bool):2*n<sourceNoetherFrequency half:=by linarith [actual_source_noether_gap half,n_pos]
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by linarith [frequency_gap half,n_pos]
private abbrev hz(half advanced:Bool)(q:ℝ):(actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=
  reverse_frequency_nonreal advanced _ (frequency_positive half) q

def jointDifference(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  completeBalancedInput s hs half advanced m ell F g x q-balancedWholeForceState s hs half advanced m ell F g x q
def jointDifferenceForcing(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  wholeInputForcing s hs half advanced m ell F g x q-balancedWholeForceSource s hs half advanced m ell F g x q

/-- The actual input and force response are one joint H0 source. The frequency derivative remains the derivative of the original complete forcing, with its own cutoff defect. -/
theorem actual_joint_difference_full_source(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    diagonalAction (jointDifference s hs half advanced m ell F g x q)=
      jointDifferenceForcing s hs half advanced m ell F g x q+
        actualFrequency advanced (sourceNoetherFrequency half) q • jointDifference s hs half advanced m ell F g x q ∧
    jointDifferenceForcing s hs half advanced m ell F g x q=
      let z:=actualFrequency advanced (sourceNoetherFrequency half) q
      wholeInputWord s hs half advanced m ell F g x
        ((reverseNativeClock-(9:ℂ) • SourceGaugeScaleTransport.generator) (normalizedForcing m ell F z (hz half advanced q) g)+
          (18:ℂ) • (z • phaseForcingFrequencySource m ell F z (hz half advanced q) g)-
          gaugeBalancedNativeForce (normalizedState m ell F z (hz half advanced q) g))+
      bracket diagonalAction (wholeInputWord s hs half advanced m ell F g x)
        (balancedInputVector m ell F z (hz half advanced q) g-balancedForceInput m ell F z (hz half advanced q) g):=by
  constructor
  · unfold jointDifference jointDifferenceForcing
    rw [map_sub,actual_whole_input_full_source,actual_balanced_whole_force_full_source,smul_sub]
    module
  · exact actual_whole_input_force_source_cancellation s hs half advanced m ell F g x q

def differenceNoetherPrice(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  18*scalarEnergy (wholeClockState s hs half advanced m ell F g x q)+
    72*wholeStep s hs half advanced m ell F g*
      (sourcePair (correctedCompleteCore s hs x.1 x.2 (X (frequencyState half advanced m ell F g q)))
        (B (wholeClockState s hs half advanced m ell F g x q))).re-
    2*(sourcePair (jointDifference s hs half advanced m ell F g x q) (B (wholeClockState s hs half advanced m ell F g x q))).re-
      2*(wholeClockWardKernel s hs half advanced m ell F g q x).re

/-- The two signed force/input legs cancel their independent force debit before any estimate. -/
theorem actual_joint_difference_noether_price(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    balancedNativeNoetherPrice s hs half advanced m ell F g x q=differenceNoetherPrice s hs half advanced m ell F g x q:=by
  have hp:=actual_balanced_whole_force_native_noether s hs half advanced m ell F g x q
  have hd:balancedWholeForceNativeDebit s hs half advanced m ell F g x q/(actualFrequency advanced (sourceNoetherFrequency half) q).im=
      2*(sourcePair (balancedWholeForceState s hs half advanced m ell F g x q) (B (wholeClockState s hs half advanced m ell F g x q))).re:=by
    rw [←hp]
    field_simp [hz half advanced q]
  have hi:correctedCompleteCore s hs x.1 x.2 (wholeSourceMap s hs half advanced m ell F g
      (balancedInputVector m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g))=
      completeBalancedInput s hs half advanced m ell F g x q:=by unfold completeBalancedInput;rfl
  unfold balancedNativeNoetherPrice differenceNoetherPrice jointDifference
  rw [hd]
  simp only [hi,sourcePair,map_sub,inner_sub_left,Complex.sub_re]
  ring

def differenceFreeUpper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  reverseNoetherFactor half*(18*scalarEnergy (wholeClockState s hs half advanced m ell F g x q)+
    72*wholeStep s hs half advanced m ell F g*
      (sourcePair (correctedCompleteCore s hs x.1 x.2 (X (frequencyState half advanced m ell F g q)))
        (B (wholeClockState s hs half advanced m ell F g x q))).re-
    2*(wholeClockWardKernel s hs half advanced m ell F g q x).re-reverseScalarReserve (wholeClockState s hs half advanced m ell F g x q))+
    reverseNoetherNormCost half*‖embed (wholeClockState s hs half advanced m ell F g x q)‖^2+
    clearedNativePrice (wholeClockState s hs half advanced m ell F g x q)+
    compensatedPrimitiveWork F (wholeClockState s hs half advanced m ell F g x q)+
    originalNormalizerPrice s hs x (wholeSourceNext s hs half advanced m ell F g q)
def differenceRadialUpper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  let a:=reverseNoetherFactor half
  let d:=jointDifference s hs half advanced m ell F g x q
  let w:=wholeClockState s hs half advanced m ell F g x q
  differenceFreeUpper s hs half advanced m ell F g x q+(56*n*a^2/3)*‖embed (phiInverseAction (U d))‖^2+
    (8*a/3)*(sourcePair (U d) (balancedOwnDefect F w)).re-2*a*(sourcePair d (bulkForceRemainder w)).re
def differenceJointLoss(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  jointForceInputLoss F (reverseNoetherFactor half) (jointDifference s hs half advanced m ell F g x q)
    (wholeClockState s hs half advanced m ell F g x q)

/-- The retained radial force square now contains the actual input-minus-response source. No independent v price survives on the right. -/
theorem actual_joint_difference_force_balance(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    coercivePrimitiveUpper s hs half advanced m ell F g x q+differenceJointLoss s hs half advanced m ell F g x q=
      differenceRadialUpper s hs half advanced m ell F g x q+
        primitiveEnergy (balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q))/21 ∧
    0 ≤ differenceJointLoss s hs half advanced m ell F g x q:=by
  have h:=actual_joint_force_input_loss F (reverseNoetherFactor half)
    (jointDifference s hs half advanced m ell F g x q) (wholeClockState s hs half advanced m ell F g x q)
  refine ⟨?_,h.2⟩
  have hc:coercivePrimitiveUpper s hs half advanced m ell F g x q=
      differenceFreeUpper s hs half advanced m ell F g x q-2*reverseNoetherFactor half*
        (sourcePair (jointDifference s hs half advanced m ell F g x q) (B (wholeClockState s hs half advanced m ell F g x q))).re:=by
    unfold coercivePrimitiveUpper
    rw [actual_joint_difference_noether_price]
    unfold differenceFreeUpper differenceNoetherPrice
    ring
  rw [hc]
  dsimp only [differenceJointLoss,differenceRadialUpper]
  linarith only [h.1]

/-- The remaining source price is the Ward of the same difference, with the full actual forcing generated above. -/
theorem actual_joint_difference_scalar_ward(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    ‖embed (phiInverseAction (U (jointDifference s hs half advanced m ell F g x q)))‖^2 ≤
      (4*affineHardyCost/(59^2*n*(sourceNoetherFrequency half-2*n)))*
        inputScalarWardPrice advanced (jointDifference s hs half advanced m ell F g x q)
          (jointDifferenceForcing s hs half advanced m ell F g x q):=
  (actual_full_source_input_scalar_gap _ (frequency_gap half) advanced q _ _
    (actual_joint_difference_full_source s hs half advanced m ell F g x q).1).2
end LowEnergy.FirstCurrentJointDifference
