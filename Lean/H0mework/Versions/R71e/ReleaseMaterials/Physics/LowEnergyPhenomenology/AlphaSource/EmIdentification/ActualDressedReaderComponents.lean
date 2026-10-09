import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalCurrent

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedReaderComponents
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussQuantumMultiplier GaussCoreDifferential CanonicalGradedSpatialSource
open scoped Matrix BigOperators
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open GaussCoreHilbert PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse
open GaussNativeMatter CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization GaussComposite.PhysicalEMPoleWard
open PreparationVacuumActionFieldLift GaussComposite.PhysicalEMGaugeRealization
open PreparationPhysicalActionUnits GaussComposite.PhysicalEMVoltage PreparationPhysicalNormalizedFullField GaussComposite.ActualDressedSourcePreparation GaussComposite.ActualDressedSourceResponse PreparationVacuumFullElectricWard


open ActualDressedActionPhase PreparationVacuumTemporalCharge PreparationVacuumLowerClassical


open ActualDressedTemporalNormalization GaussFockPair PreparationVacuumSourceActionJets
open MeasureTheory Filter Set


open ActualDressedTemporalForm ActualDressedJointTemporal ActualDressedJointOrbitCurrent
open ActualDressedFullCoulomb PreparationVacuumWeightedChargeActionWard
open PreparationVacuumSourceChargeWard PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumFullFieldRiesz PreparationVacuumNoetherChart
open scoped Topology InnerProductSpace
open PreparationVacuumFieldConstraintResponse CanonicalPhysicalYResolvent PreparationVacuumSourcePreparedResponse
open CanonicalPreparationCore.Completed CanonicalScalarPreparation GaussComposite.SourceGraph
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceProfile finiteFull sourceDressedResponse chargeReader


open PreparationVacuumFieldCovector PreparationVacuumRawJointFeedback PreparationVacuumCausalFieldResponse
open PreparationVacuumActionDecomposition PreparationVacuumGradedTransport
open ActualDressedTemporalCurrent

private theorem fiber_parameter_current (f : Field289) (p : PhysicalMomentum)
    (l r : QuantumTest) (z : SourceCoordinateSlice) :
    parameterCurrent (fiberSample (actualFiber p) l r) f z=
      sampleCurrent (fiberSample (actualFiber p) l r) f z := by
  exact parameterCurrent_eq (fiberSample (actualFiber p) l r) l
    (fun g t x hx hy=>fiberSample_param (actualFiber p) (actualFiber_smooth p) l r
      (fun u : Parameter=>fieldCoordinateCurve g u.1 u.2) Prod.snd
      (t,x) hy (field_curve_smooth g t ⟨x,hx⟩) contDiffAt_snd)
    (fun x=>(fiberSample_param (actualFiber p) (actualFiber_smooth p) l r id (fun _=>x.val)
      x.val x.property contDiffAt_id contDiffAt_const).differentiableAt (by simp))
    (fiberSample_zero_outside (actualFiber p) l r) f z

/-- The actual configuration-density derivative and missing action-state fiber direction. -/
def temporalFiberResidualSample (a : Fin 12) (p : PhysicalMomentum)
    (l r : QuantumTest) (z : SourceCoordinateSlice) : ℂ :=
  densityCurrent (temporalField a) p l r z-
    pairSample z (l z) (quantizer (symbolFirst p (sourceState z) (complement (temporalField a) z)) (r z))

theorem temporal_fiber_residual_source (a : Fin 12) (p : PhysicalMomentum)
    (l r : QuantumTest) (z : SourceCoordinateSlice) :
    temporalFiberResidualSample a p l r z=
      parameterCurrent (fiberSample (actualFiber p) l r) (temporalField a) z+
        densityPair l (familyCore (temporalField a) p r) z := by
  rw [fiber_parameter_current]
  by_cases inside : z∈physicalChart
  · have paid:=fiber_sample_mother_balance (temporalField a) p l r ⟨z,inside⟩
    change sampleCurrent (fiberSample (actualFiber p) l r) (temporalField a) z+
      pairSample z (l z) (quantizer (symbolFirst p (sourceState z) (complement (temporalField a) z)) (r z))=
      densityCurrent (temporalField a) p l r z-pairSample z (l z) (familyCore (temporalField a) p r z) at paid
    rw [←pairSample_source]
    unfold temporalFiberResidualSample
    linear_combination -paid
  · have zero : l z=0 := image_eq_zero_of_notMem_tsupport (fun h=>inside (l.tsupport_subset h))
    have pc:=parameterCurrent_zero (fiberSample (actualFiber p) l r) l
      (fiberSample_zero_outside (actualFiber p) l r) (temporalField a) z
      (fun h=>inside (l.tsupport_subset h))
    rw [fiber_parameter_current] at pc
    rw [pc,←pairSample_source,zero]
    simp only [temporalFiberResidualSample,densityCurrent,zero,pairSample_zero_left,PiLp.zero_apply,
      star_zero,mul_zero,zero_mul,Finset.sum_const_zero,sub_zero,zero_add]

private theorem fiber_parameter_integrable (f : Field289) (p : PhysicalMomentum) (l r : QuantumTest) :
    Integrable (parameterCurrent (fiberSample (actualFiber p) l r) f) GaussHistoryHilbert.configurationMeasure := by
  exact parameterCurrent_integrable (fiberSample (actualFiber p) l r) l
    (fun g t x hx hy=>fiberSample_param (actualFiber p) (actualFiber_smooth p) l r
      (fun u : Parameter=>fieldCoordinateCurve g u.1 u.2) Prod.snd
      (t,x) hy (field_curve_smooth g t ⟨x,hx⟩) contDiffAt_snd)
    (fiberSample_zero_outside (actualFiber p) l r) f

theorem temporal_fiber_residual_integrable (a : Fin 12) (p : PhysicalMomentum) (l r : QuantumTest) :
    Integrable (temporalFiberResidualSample a p l r) GaussHistoryHilbert.configurationMeasure := by
  apply ((fiber_parameter_integrable (temporalField a) p l r).add
    (densityPair_integrable l (familyCore (temporalField a) p r))).congr
  exact Filter.Eventually.of_forall (fun z=>(temporal_fiber_residual_source a p l r z).symm)

/-- The full fiber response is generated from density and missing fiber directions, with the temporal current subtracted once. -/
theorem temporal_fiber_first (a : Fin 12) (p : PhysicalMomentum) (l r : QuantumTest) :
    (fiberFieldJets (temporalField a) (actualFiber p) (actualFiber_smooth p) l r).first 0=
      (∫z,temporalFiberResidualSample a p l r z ∂GaussHistoryHilbert.configurationMeasure)-
        sourcePair l (familyCore (temporalField a) p r) := by
  change (∫z,parameterCurrent (fiberSample (actualFiber p) l r) (temporalField a) z
    ∂GaussHistoryHilbert.configurationMeasure)=_
  calc
    _=∫z,(temporalFiberResidualSample a p l r z-densityPair l (familyCore (temporalField a) p r) z)
        ∂GaussHistoryHilbert.configurationMeasure := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      dsimp only
      rw [temporal_fiber_residual_source]
      ring
    _=_ := by
      rw [integral_sub (temporal_fiber_residual_integrable a p l r)
        (densityPair_integrable l (familyCore (temporalField a) p r)),sourcePair_integral]

/-- Every compensation is an original source sector: native/coframe, density plus fiber complement, retained fiber, non-scalar time mismatch, and full pair term. -/
def temporalReaderCompensationForm (a : Fin 12) (p : PhysicalMomentum) (l r : QuantumTest) : ℂ :=
  (nativeFieldJets (temporalField a) l r).first 0+
    (coframeFieldJets (temporalField a) l r).first 0+
    (∫z,temporalFiberResidualSample a p l r z ∂GaussHistoryHilbert.configurationMeasure)-
    (fiberFieldJets (temporalField a) retainedCoefficient retainedCoefficient_smooth l r).first 0+
    sourcePair l ((sourceTimeWeightCore-(LinearMap.id : QuantumTest→ₗ[ℂ]QuantumTest)) (familyCore (temporalField a) p r))-
    sourcePair l (normalChargeCore a r)

/-- The original full field first jet is the negative raw temporal Noether action plus these source-generated sectors. -/
theorem temporal_reader_form_generated (a : Fin 12) (p : PhysicalMomentum) (l r : QuantumTest) :
    (fieldJets (temporalField a) p l r).first 0=
      -noetherForm (temporalField a) p l r 0+temporalReaderCompensationForm a p l r := by
  change (nativeFieldJets (temporalField a) l r).first 0+
    (coframeFieldJets (temporalField a) l r).first 0+
    (fiberFieldJets (temporalField a) (actualFiber p) (actualFiber_smooth p) l r).first 0-
    (fiberFieldJets (temporalField a) retainedCoefficient retainedCoefficient_smooth l r).first 0=_
  rw [temporal_fiber_first,temporal_raw_noether_return]
  simp only [temporalReaderCompensationForm,LinearMap.sub_apply,LinearMap.id_apply,sourcePair,map_sub,inner_sub_right]
  ring

/-- The same original source frame carries the complete reader compensation. -/
def temporalReaderCompensation (a : Fin 12) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  finiteRiesz F (fun i j=>temporalReaderCompensationForm a p (frameTest F i) (frameTest F j))

private theorem finiteRiesz_neg_add (F : GaussUnitaryHistory.Index)
    (A B : FrameIndex F→FrameIndex F→ℂ) :
    finiteRiesz F (fun i j=> -A i j+B i j)= -finiteRiesz F A+finiteRiesz F B := by
  unfold finiteRiesz
  simp only [add_smul,neg_smul,Finset.sum_add_distrib,Finset.sum_neg_distrib]

attribute [local irreducible] currentRestriction noetherReader temporalReaderCompensation
  nativeFieldJets coframeFieldJets fiberFieldJets fieldJets

theorem temporal_reader_generated (a : Fin 12) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    currentRestriction (temporalField a) p F 0=
      -noetherReader (temporalField a) p F 0+temporalReaderCompensation a p F := by
  unfold currentRestriction noetherReader temporalReaderCompensation
  rw [←finiteRiesz_neg_add]
  apply congrArg (finiteRiesz F)
  funext i j
  exact temporal_reader_form_generated a p (frameTest F i) (frameTest F j)

/-- The compensation price is the original finite source entries, with no caller-selected coefficient. -/
theorem temporal_reader_compensation_price (a : Fin 12) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ‖temporalReaderCompensation a p F‖≤finitePrice F
      (fun i j=>temporalReaderCompensationForm a p (frameTest F i) (frameTest F j)) := by
  unfold temporalReaderCompensation
  exact finiteRiesz_price F (fun i j=>temporalReaderCompensationForm a p (frameTest F i) (frameTest F j))

end LowEnergy.GaussComposite.ActualDressedReaderComponents
