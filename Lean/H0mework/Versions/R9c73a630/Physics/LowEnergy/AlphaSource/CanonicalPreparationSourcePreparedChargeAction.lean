import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalChargeNormalization

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceChargeWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert CanonicalGradedSpatialSource
open FullQuantum.StateGreen PreparationVacuumMixedFieldReturn PreparationVacuumOriginalDensity
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve PreparationVacuumHalfDensityFiber
open PreparationVacuumNoetherChart PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumTemporalCharge PreparationVacuumFullElectricWard CanonicalGradedCharge PreparationVacuumLowerClassical
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
abbrev ChargeOperator:=H→L[ℂ] H
local instance : NormedAlgebra ℝ ChargeOperator:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] noetherReader noetherReaderContact PreparationVacuumRawJointFeedback.rawReader rawReaderContact
  rawActionSymbol noetherContactSymbol densityActionMatrix rawMomentumMatrix sourceActionWeight
  noetherPreparedCurrent noetherPreparedSlope physicalTime timeSlope jointResolvent jointCurrent
  preparedDual preparedPrimal independentDual

def weightedTemporalForm (a : Fin 12) (l r : QuantumTest) : ℂ:=
  ∫z,pairSample z (l z)
    (quantizer (SourceRealScalarFock.branches (rawMomentumMatrix (sourceState z))*chargeMatrix (originalUnit a)) (r z))
    ∂GaussHistoryHilbert.configurationMeasure

theorem temporalForm_source (a : Fin 12) (p : PhysicalMomentum) (l r : QuantumTest) :
    noetherForm (temporalField a) p l r 0=weightedTemporalForm a l r :=by
  unfold noetherForm weightedTemporalForm
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change noetherSample (temporalField a) p l r (0,z)=
    pairSample z (l z) (quantizer (SourceRealScalarFock.branches (rawMomentumMatrix (sourceState z))*
      chargeMatrix (originalUnit a)) (r z))
  by_cases inside : z∈tsupport l
  · have valid : sourceState z∈validStates:=sourceState_valid ⟨z,l.tsupport_subset inside⟩
    rw [noetherSample]
    rw [noetherFiber_source _ _ ⟨z,l.tsupport_subset inside⟩]
    change pairSample z (l z) (quantizer (rawActionSymbol (temporalField a) p (ambientState (0,z))) (r z))=_
    rw [ambientState_zero,←transportedRawSymbol_source (temporalField a) (sourceState z) valid p,
      transportedTemporalSymbol a _ _ valid p]
  · simp only [noetherSample,image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

theorem temporalReader_source (a : Fin 12) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReader (temporalField a) p F 0=
      finiteRiesz F (fun i j=>weightedTemporalForm a (frameTest F i) (frameTest F j)) :=by
  unfold noetherReader
  exact congrArg (finiteRiesz F) (funext (fun i=>funext (fun j=>temporalForm_source a p _ _)))

theorem temporalReader_momentum_independent (a : Fin 12) (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReader (temporalField a) p F 0=noetherReader (temporalField a) k F 0 :=by
  rw [temporalReader_source,temporalReader_source]

/-- No occupancy restriction is taken when reading the canonical charge factor. -/
theorem weightedTemporalForm_fullCAR (a : Fin 12) (l r : QuantumTest) :
    weightedTemporalForm a l r=
      ∫z,pairSample z (l z)
        (quantizer (SourceRealScalarFock.branches (rawMomentumMatrix (sourceState z)))
          (quantizer (chargeMatrix (originalUnit a)) (r z))-
        pairFiber (SourceRealScalarFock.branches (rawMomentumMatrix (sourceState z))) (chargeMatrix (originalUnit a)) (r z))
        ∂GaussHistoryHilbert.configurationMeasure :=by
  unfold weightedTemporalForm
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have ordered:=congrArg (fun T : FockFiber→L[ℂ] FockFiber=>T (r z))
    (quantized_normal_order (SourceRealScalarFock.branches (rawMomentumMatrix (sourceState z))) (chargeMatrix (originalUnit a)))
  simp only [mul_apply_eq_comp,add_apply] at ordered
  exact congrArg (pairSample z (l z)) (eq_sub_of_add_eq ordered.symm)

theorem temporalContactForm_zero (a : Fin 12) (force : Field289) (p : PhysicalMomentum) (l r : QuantumTest) :
    noetherContactForm (temporalField a) force p l r=0 :=by
  unfold noetherContactForm
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro z
  change pairSample z (l z) (quantizer (noetherContactSymbol (temporalField a) force (sourceState z) p) (r z))=0
  by_cases inside : z∈tsupport l
  · rw [temporalNoetherContactSymbol a force ⟨z,l.tsupport_subset inside⟩ p,map_zero,zero_apply]
    simp only [pairSample,map_zero,WithLp.ofLp_zero,Pi.zero_apply,zero_apply,mul_zero,Finset.sum_const_zero]
  · simp only [image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

theorem temporalContactReader_zero (a : Fin 12) (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReaderContact (temporalField a) force p F=0 :=by
  rw [noetherReaderContact_source]
  simp only [temporalContactForm_zero,finiteRiesz,zero_smul,Finset.sum_const_zero]

/-- The two time variations and the two inverse variations survive the contact cancellation. -/
def temporalPropagationKernel (q : PhysicalResponsePoint) (a : Fin 12) (force : Field289) (t : ℝ) : ChargeOperator:=
  let J:=noetherReader (temporalField a) q.p q.F 0
  timeSlope force (q.p+q.k) q.F (-t)*jointResolvent (q.p+q.k) q.F q.z 0*J*
    jointResolvent q.p q.F q.w 0*physicalTime q.p q.F t 0+
  physicalTime (q.p+q.k) q.F (-t) 0*(-(jointResolvent (q.p+q.k) q.F q.z 0*
    jointCurrent (q.p+q.k) q.F q.z 0 force*jointResolvent (q.p+q.k) q.F q.z 0))*J*
    jointResolvent q.p q.F q.w 0*physicalTime q.p q.F t 0+
  physicalTime (q.p+q.k) q.F (-t) 0*jointResolvent (q.p+q.k) q.F q.z 0*J*
    (-(jointResolvent q.p q.F q.w 0*jointCurrent q.p q.F q.w 0 force*jointResolvent q.p q.F q.w 0))*
      physicalTime q.p q.F t 0+
  physicalTime (q.p+q.k) q.F (-t) 0*jointResolvent (q.p+q.k) q.F q.z 0*J*
    jointResolvent q.p q.F q.w 0*timeSlope force q.p q.F t

theorem temporalPreparedSlope_source (q : PhysicalResponsePoint) (a : Fin 12) (force : Field289) (t : ℝ) :
    noetherPreparedSlope q (temporalField a) force t=
      sourceRead q (temporalPropagationKernel q a force t) :=by
  rw [noetherPreparedSlope,temporalContactReader_zero]
  simp only [zero_apply,map_zero,add_zero]
  simp only [densitySlope,dualSlope,preparedDual,preparedPrimal,independentDual,primalSlope,
    temporalPropagationKernel,noetherReader_source,sourceRead,
    mul_apply_eq_comp,add_apply,map_add,inner_add_right,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply,innerSL_apply_apply]
  abel

theorem temporalPreparedCurrent_generated (q : PhysicalResponsePoint) (a : Fin 12) (force : Field289) (t : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>noetherPreparedCurrent q (temporalField a) (r • force) t)
      (sourceRead q (temporalPropagationKernel q a force t)) 0 :=by
  rw [←temporalPreparedSlope_source]
  exact noetherPreparedCurrent_generated q (temporalField a) force t hz hw

theorem temporalResponseJet_value (q : PhysicalResponsePoint) (a : Fin 12) (force : Field289) (t : ℝ) :
    (preparedSlopeTimeJet q (temporalField a) force t).value=
      sourceRead q (temporalPropagationKernel q a force t) :=by
  rw [preparedSlopeTimeJet_value,temporalPreparedSlope_source]

end LowEnergy.PreparationVacuumSourceChargeWard
