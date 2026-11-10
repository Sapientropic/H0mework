import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualRestLightWholePartition
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualRestLightPreparedKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceLightCircuit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussFockLift
open FullQuantum.StateGreen ActualElectronPhysicalNormalization
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve PreparationVacuumGaugeSourceInjection
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumFullFieldRiesz
open PreparationVacuumNoetherChart PreparationVacuumHalfDensityFiber ActualSourcePreparationBridge
open PreparationVacuumSourceActionJets
open ActualCompositeFieldCurrent ActualElectronPhysicalJointInverse MixedSpectatorCandidate
open CanonicalGradedSpatialSource MeasureTheory Filter Set GaussHistoryHilbert
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance materialFinite : FiniteDimensional ℂ FullMaterialMatrix:=Matrix.finiteDimensional
local instance sourceFinite : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
attribute [local irreducible] transportedRawSymbol noetherContactSymbol rawActionSymbol candidate
  sourceState actualElectronAmputatedLeg sourceRestLightMap sourceRestRemainderMap

/-- T is evaluated on the original transported full source symbol, with its original configuration argument. -/
def projectedNoetherFiber (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (reader : Field289) (p : PhysicalMomentum) (u : JointParameter) : FiberOp :=
  quantizer (T (transportedRawSymbol reader (sourceState u.2) (ambientState u) p))

private theorem projected_fiber_smooth (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (reader : Field289) (p : PhysicalMomentum) (u : JointParameter)
    (base : u.2∈physicalChart) (valid : ambientState u∈validStates) :
    ContDiffAt ℝ ∞ (projectedNoetherFiber T reader p) u := by
  unfold projectedNoetherFiber transportedRawSymbol
  exact (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp u
    ((T.restrictScalars ℝ).contDiff.contDiffAt.comp u
      ((rawFourier p).toContinuousLinearMap.contDiff.contDiffAt.comp u
        (contDiffAt_pi.mpr (fun i=>transportedDensity_smooth reader i u base valid))))

theorem projected_noether_fiber_generated (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (reader force : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>projectedNoetherFiber T reader p (r • force,z.val))
      (quantizer (T (noetherContactSymbol reader force (sourceState z.val) p))) 0 := by
  have material:=(T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (noetherContactSymbol_generated reader force z p)
  have original:=(quantizer.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 material
  have ray (r : ℝ) : ambientState (r • force,z.val)=sourceState z.val+r • fieldDirection force := by
    simp only [ambientState,map_smul];rfl
  have aligned : (fun r : ℝ=>projectedNoetherFiber T reader p (r • force,z.val))=
      fun r : ℝ=>quantizer (T (transportedRawSymbol reader (sourceState z.val)
        (sourceState z.val+r • fieldDirection force) p)) := by
    funext r;unfold projectedNoetherFiber;rw [ray]
  rw [aligned]
  convert! original using 1

private def projectedSample (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (u : JointParameter) : ℂ :=
  pairSample u.2 (a u.2) (projectedNoetherFiber T reader p u (b u.2))

private theorem projected_sample_zero (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (z : SourceCoordinateSlice) (outside : z∉tsupport a) :
    projectedSample T reader p a b (h,z)=0 := by
  simp only [projectedSample,image_eq_zero_of_notMem_tsupport outside,pairSample_zero_left]

private theorem projected_sample_smooth (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (z : SourceCoordinateSlice) (small : ‖h‖<ambientRadius a) :
    ContDiffAt ℝ ∞ (projectedSample T reader p a b) (h,z) := by
  by_cases inside : z∈tsupport a
  · let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
    have coefficient:=R.contDiff.contDiffAt.comp (h,z)
      (projected_fiber_smooth T reader p (h,z) (a.tsupport_subset inside)
        (ambientRadius_valid a h z small.le inside))
    exact pairSample_param Prod.snd _ _ (h,z) (a.tsupport_subset inside) contDiffAt_snd
      (a.contDiff.contDiffAt.comp (h,z) contDiffAt_snd)
      (coefficient.clm_apply (b.contDiff.contDiffAt.comp (h,z) contDiffAt_snd))
  · apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      ((isClosed_tsupport a).isOpen_compl.mem_nhds inside)] with u hu
    exact projected_sample_zero T reader p a b u.1 u.2 hu

def projectedNoetherForm (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) : ℂ :=
  ∫z,projectedSample T reader p a b (h,z) ∂GaussHistoryHilbert.configurationMeasure

def projectedNoetherContactForm (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  ∫z,pairSample z (a z) (quantizer (T (noetherContactSymbol reader force (sourceState z) p)) (b z))
    ∂GaussHistoryHilbert.configurationMeasure

private theorem projected_form_C2 (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    ContDiffAt ℝ 2 (projectedNoetherForm T reader p a b) 0 :=
  source_integral_C2 _ (tsupport a) a.hasCompactSupport (ambientRadius a) (ambientRadius_positive a)
    (projected_sample_smooth T reader p a b) (projected_sample_zero T reader p a b)

theorem projected_noether_form_generated (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    HasDerivAt (fun r : ℝ=>projectedNoetherForm T reader p a b (r • force))
      (projectedNoetherContactForm T reader force p a b) 0 := by
  have differential:=source_integral_fderivative (projectedSample T reader p a b) (tsupport a) a.hasCompactSupport
    (ambientRadius a) (ambientRadius_positive a) (projected_sample_smooth T reader p a b)
    (projected_sample_zero T reader p a b) 0 (by simpa only [norm_zero] using half_pos (ambientRadius_positive a))
  have original:=differential.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
  have integrable:=parameter_slice_integrable (parameterPartial (projectedSample T reader p a b))
    (tsupport a) a.hasCompactSupport 0
    (fun z=>parameterPartial_smooth _ _ (projected_sample_smooth T reader p a b 0 z
      (by simpa using ambientRadius_positive a)))
    (parameterPartial_zero _ _ (isClosed_tsupport a) (projected_sample_zero T reader p a b))
  have each (z : SourceCoordinateSlice) : parameterPartial (projectedSample T reader p a b) (0,z) force=
      pairSample z (a z) (quantizer (T (noetherContactSymbol reader force (sourceState z) p)) (b z)) := by
    by_cases inside : z∈tsupport a
    · have d:=parameterPartial_derivative (projectedSample T reader p a b) 0 z
        (projected_sample_smooth T reader p a b 0 z (by simpa using ambientRadius_positive a))
      have first:=d.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
      let E:=(ContinuousLinearMap.apply ℂ FockFiber (b z)).restrictScalars ℝ
      let P:=(pairRight z (a z)).restrictScalars ℝ
      have second:=P.hasFDerivAt.comp_hasDerivAt 0 (E.hasFDerivAt.comp_hasDerivAt 0
        (projected_noether_fiber_generated T reader force p ⟨z,a.tsupport_subset inside⟩))
      exact first.unique second
    · rw [parameterPartial_zero _ _ (isClosed_tsupport a) (projected_sample_zero T reader p a b) 0 z inside]
      simp only [image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left,zero_apply]
  have value : (∫z,parameterPartial (projectedSample T reader p a b) (0,z)
      ∂GaussHistoryHilbert.configurationMeasure) force=projectedNoetherContactForm T reader force p a b := by
    rw [ContinuousLinearMap.integral_apply integrable]
    exact integral_congr_ae (Filter.Eventually.of_forall each)
  exact original.congr_deriv value

def projectedNoetherReader (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) : H→L[ℂ]H :=
  finiteRiesz F (fun i j=>projectedNoetherForm T reader p (frameTest F i) (frameTest F j) h)

def projectedNoetherReaderContact (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  finiteRiesz F (fun i j=>projectedNoetherContactForm T reader force p (frameTest F i) (frameTest F j))

theorem projected_noether_reader_generated (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    HasDerivAt (fun r : ℝ=>projectedNoetherReader T reader p F (r • force))
      (projectedNoetherReaderContact T reader force p F) 0 := by
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact (projected_noether_form_generated T reader force p (frameTest F i) (frameTest F j)).smul_const
    (InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))

abbrev sourceLightNoetherReader:=projectedNoetherReader sourceRestLightMap
abbrev sourceLightNoetherReaderContact:=projectedNoetherReaderContact sourceRestLightMap
abbrev sourceRemainderNoetherReader:=projectedNoetherReader sourceRestRemainderMap
abbrev sourceRemainderNoetherReaderContact:=projectedNoetherReaderContact sourceRestRemainderMap

/-- The actual N3 Gram reduces the source light current to its exact finite CAR kernel under the original configuration probability. -/
theorem actual_prepared_light_noether_integral (leg : CompositeLeg) (reader : Field289) (p : PhysicalMomentum) :
    projectedNoetherForm sourceRestLightMap reader p (actualElectronAmputatedLeg leg) (actualElectronAmputatedLeg leg) 0=
      ∫z,(actualMaterialProbabilityDensity leg z/2)*inner ℂ (candidate leg.dual)
        (projectedNoetherFiber sourceRestLightMap reader p (0,z) (candidate leg.dual))
        ∂GaussHistoryHilbert.configurationMeasure := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z=>actual_material_pair_sample leg z
    (projectedNoetherFiber sourceRestLightMap reader p (0,z))

/-- The full transported contact, rather than raw Hessian contact alone, enters the same actual N3 integral. -/
theorem actual_prepared_light_noether_contact_integral (leg : CompositeLeg)
    (reader force : Field289) (p : PhysicalMomentum) :
    projectedNoetherContactForm sourceRestLightMap reader force p
      (actualElectronAmputatedLeg leg) (actualElectronAmputatedLeg leg)=
      ∫z,(actualMaterialProbabilityDensity leg z/2)*inner ℂ (candidate leg.dual)
        (quantizer (sourceRestLightMap (noetherContactSymbol reader force (sourceState z) p))
          (candidate leg.dual)) ∂GaussHistoryHilbert.configurationMeasure := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z=>actual_material_pair_sample leg z
    (quantizer (sourceRestLightMap (noetherContactSymbol reader force (sourceState z) p)))


theorem projected_noether_form_integrable (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289)
    (small : ‖h‖<ambientRadius a) :
    Integrable (fun z=>pairSample z (a z) (projectedNoetherFiber T reader p (h,z) (b z)))
      GaussHistoryHilbert.configurationMeasure :=
  parameter_slice_integrable (projectedSample T reader p a b) (tsupport a) a.hasCompactSupport h
    (fun z=>projected_sample_smooth T reader p a b h z small) (projected_sample_zero T reader p a b)

/-- Source frame CAR covariance eliminates the full material sum from the actual light current integral. -/
theorem actual_prepared_light_noether_finite_integral (leg : CompositeLeg) (reader : Field289) (p : PhysicalMomentum) :
    projectedNoetherForm sourceRestLightMap reader p (actualElectronAmputatedLeg leg) (actualElectronAmputatedLeg leg) 0=
      ∫z,(actualMaterialProbabilityDensity leg z/2)*sourceRestLightCandidateRead leg.dual
        (transportedRawSymbol reader (sourceState z) (ambientState (0,z)) p)
        ∂GaussHistoryHilbert.configurationMeasure := by
  rw [actual_prepared_light_noether_integral]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change (actualMaterialProbabilityDensity leg z/2)*inner ℂ (candidate leg.dual)
    (quantizer (sourceRestLightMap (transportedRawSymbol reader (sourceState z) (ambientState (0,z)) p))
      (candidate leg.dual))=_
  rw [source_rest_light_map_value,source_rest_light_candidate_kernel]

/-- The very same finite CAR covariance consumes the full transported contact at every configuration. -/
theorem actual_prepared_light_noether_contact_finite_integral (leg : CompositeLeg)
    (reader force : Field289) (p : PhysicalMomentum) :
    projectedNoetherContactForm sourceRestLightMap reader force p
      (actualElectronAmputatedLeg leg) (actualElectronAmputatedLeg leg)=
      ∫z,(actualMaterialProbabilityDensity leg z/2)*sourceRestLightCandidateRead leg.dual
        (noetherContactSymbol reader force (sourceState z) p) ∂GaussHistoryHilbert.configurationMeasure := by
  rw [actual_prepared_light_noether_contact_integral]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change (actualMaterialProbabilityDensity leg z/2)*inner ℂ (candidate leg.dual)
    (quantizer (sourceRestLightMap (noetherContactSymbol reader force (sourceState z) p))
      (candidate leg.dual))=_
  rw [source_rest_light_map_value,source_rest_light_candidate_kernel]

end LowEnergy.GaussComposite.ActualSourceLightCircuit
