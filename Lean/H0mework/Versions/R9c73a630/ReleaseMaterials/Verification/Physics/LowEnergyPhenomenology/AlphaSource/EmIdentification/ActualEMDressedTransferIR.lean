import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMJointCurrentMomentum
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMMovingIR

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMDressedTransferIR
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumPropagationPencil
open PreparationVacuumFieldPerturbation PreparationVacuumFieldConstraintResponse
open PreparationVacuumFullPoleContinuation PreparationVacuumNoetherChart
open PreparationVacuumGaugeSourceInjection PreparationVacuumSourceFieldFamily
open PreparationVacuumStaticVoltageSource PreparationVacuumActionFieldLift
open PreparationVacuumOriginalGreenFeedback SourcePropagationTimeDependentFeedback
open SourcePropagationNoetherTime ActualDressedNoether ActualDressedFullCoulomb
open ActualEMJointCurrentMomentum ActualEMCauchyDynamic ActualEMDressedGaugePole
open ActualEMCarrierOwn ActualEMGaugeCurvature
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumNativePoleTensor PreparationVacuumSoftPoleSelection
open PreparationPhysicalCurvatureSheetLimit PreparationPhysicalNativePolarizationEmitter
open MeasureTheory Filter Set
open scoped Matrix BigOperators Topology Interval
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup (Field289→L[ℝ](H→L[ℂ]H)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Field289→L[ℝ](H→L[ℂ]H)) := ContinuousLinearMap.toNormedSpace
attribute [local irreducible] jointCurrent jointResolvent jointGenerator rawReader rawReaderContact
  noetherReaderContact noetherReader sourceVoltageSpatialVector
  sourceVoltageTemporalVector voltageNativeTimeJet noetherHistoryOperatorJet
  dressedVoltageForcing dressedGaugeCurrent dressedGaugePole

private theorem voltage_value_continuous (imaginary : Bool) :
    Continuous (fun kt : PhysicalMomentum × ℝ =>
      (voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial kt.1) imaginary kt.2).value) := by
  apply continuous_pi
  intro i
  unfold voltageNativeTimeJet
  change Continuous (fun kt : PhysicalMomentum × ℝ =>
    voltageQuadrature imaginary (sourceVoltageSpatialVector (PreparationVacuumPhysicalFeedback.physicalSpatial kt.1) i)+
    kt.2*voltageQuadrature imaginary (sourceVoltageTemporalVector i))
  unfold voltageQuadrature sourceVoltageSpatialVector PreparationVacuumPhysicalFeedback.physicalSpatial
  simp only [Pi.add_apply,Pi.single_apply]
  cases imaginary <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> split_ifs <;> fun_prop

private theorem raw_contact_linear (reader force : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    rawReaderContact reader force p F=(fderiv ℝ (rawReader reader p F) 0) force :=
  (readerDifferential_contact reader force p F).symm

private theorem noether_contact_linear (reader force : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    noetherReaderContact reader force p F=(fderiv ℝ (noetherReader reader p F) 0) force := by
  unfold noetherReaderContact
  rfl

private theorem time_left_continuous (event : DressedEvent) :
    Continuous (fun kt : PhysicalMomentum × ℝ =>physicalTime (event.momentum-kt.1) event.frame kt.2 0) :=
  (actualJointTime_continuous event.frame).comp
    ((continuous_const.sub continuous_fst).prodMk continuous_snd)

private theorem current_left_continuous (event : DressedEvent) (imaginary : Bool) (z : ℂ) :
    Continuous (fun kt : PhysicalMomentum × ℝ =>jointCurrent (event.momentum-kt.1) event.frame z 0
      (voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial kt.1) imaginary kt.2).value) :=
  ((joint_current_momentum_continuous event.frame z).comp
    (continuous_const.sub continuous_fst)).clm_apply (voltage_value_continuous imaginary)

private theorem primal_continuous (event : DressedEvent) (imaginary : Bool) :
    Continuous (fun kt : PhysicalMomentum × ℝ =>orderedPrimal (dressedKinematicPoint event kt.1)
      (fun s=>(voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial kt.1) imaginary s).value) kt.2) := by
  have temporal : Continuous (fun kt : PhysicalMomentum × ℝ =>physicalTime event.momentum event.frame kt.2 0) :=
    (actualJointTime_continuous event.frame).comp (continuous_const.prodMk continuous_snd)
  have negative : Continuous (fun kt : PhysicalMomentum × ℝ =>physicalTime event.momentum event.frame (-kt.2) 0) :=
    (actualJointTime_continuous event.frame).comp (continuous_const.prodMk continuous_snd.neg)
  have current := (jointCurrent event.momentum event.frame 0 0).continuous.comp (voltage_value_continuous imaginary)
  have integrand := (negative.mul (current.const_smul (-Complex.I))).mul temporal
  have primitive := intervalIntegral.continuous_parametric_primitive_of_continuous (a₀:=0)
    (μ:=volume) (f:=fun (k : PhysicalMomentum) (s : ℝ)=>physicalTime event.momentum event.frame (-s) 0*
      ((-Complex.I) • jointCurrent event.momentum event.frame 0 0
        (voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial k) imaginary s).value)*
      physicalTime event.momentum event.frame s 0) integrand
  change Continuous (fun kt : PhysicalMomentum × ℝ =>physicalTime event.momentum event.frame kt.2 0*
    ∫s in (0:ℝ)..kt.2,physicalTime event.momentum event.frame (-s) 0*
      ((-Complex.I) • jointCurrent event.momentum event.frame 0 0
        (voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial kt.1) imaginary s).value)*
      physicalTime event.momentum event.frame s 0)
  exact temporal.mul primitive

private theorem dual_continuous (event : DressedEvent) (imaginary : Bool) :
    Continuous (fun kt : PhysicalMomentum × ℝ =>orderedDual (dressedKinematicPoint event kt.1)
      (fun s=>(voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial kt.1) imaginary s).value) kt.2) := by
  have temporal := time_left_continuous event
  have negative := temporal.comp (continuous_fst.prodMk continuous_snd.neg)
  have current := current_left_continuous event imaginary 0
  have integrand := (negative.mul (current.const_smul (-Complex.I)).neg).mul temporal
  have primitive := intervalIntegral.continuous_parametric_primitive_of_continuous (a₀:=0)
    (μ:=volume) (f:=fun (k : PhysicalMomentum) (s : ℝ)=>physicalTime (event.momentum-k) event.frame (-s) 0*
      (-((-Complex.I) • jointCurrent (event.momentum-k) event.frame 0 0
        (voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial k) imaginary s).value))*
      physicalTime (event.momentum-k) event.frame s 0) integrand
  change Continuous (fun kt : PhysicalMomentum × ℝ =>(∫s in (0:ℝ)..kt.2,
    physicalTime (event.momentum-kt.1) event.frame (-s) 0*
      (-((-Complex.I) • jointCurrent (event.momentum-kt.1) event.frame 0 0
        (voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial kt.1) imaginary s).value))*
      physicalTime (event.momentum-kt.1) event.frame s 0)*
    physicalTime (event.momentum-kt.1) event.frame (-kt.2) 0)
  exact primitive.mul negative

private theorem middle_continuous (event : DressedEvent) (reader : Field289) (imaginary : Bool) :
    Continuous (fun kt : PhysicalMomentum × ℝ =>historyMiddle (dressedKinematicPoint event kt.1) reader
      (fun s=>(voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial kt.1) imaginary s).value) kt.2) := by
  have resolvent := (actualJointResolvent_continuous event.frame event.energy event.nonreal).comp
    (show Continuous (fun kt : PhysicalMomentum × ℝ =>event.momentum-kt.1) from continuous_const.sub continuous_fst)
  have initial := (voltage_value_continuous imaginary).comp
    (show Continuous (fun kt : PhysicalMomentum × ℝ =>(kt.1,(0:ℝ))) from continuous_fst.prodMk continuous_const)
  have left := ((joint_current_momentum_continuous event.frame event.energy).comp
    (show Continuous (fun kt : PhysicalMomentum × ℝ =>event.momentum-kt.1) from continuous_const.sub continuous_fst)).clm_apply initial
  have right := (jointCurrent event.momentum event.frame event.energy 0).continuous.comp initial
  have contact := (fderiv ℝ (rawReader reader event.momentum event.frame) 0).continuous.comp
    (voltage_value_continuous imaginary)
  simp only [historyMiddle,dressedKinematicPoint,←sub_eq_add_neg,raw_contact_linear]
  exact (((resolvent.mul left).mul resolvent).neg.mul continuous_const |>.mul continuous_const).add
    ((resolvent.mul contact).mul continuous_const) |>.add
      ((resolvent.mul continuous_const).mul ((continuous_const.mul right).mul continuous_const).neg)

/-- Both original time-ordered legs and the canonical Noether contact vary continuously with this actual transfer. -/
theorem dressed_voltage_operator_transfer_continuous (event : DressedEvent) (reader : Field289)
    (imaginary : Bool) :
    Continuous (fun kt : PhysicalMomentum × ℝ =>
      (noetherHistoryOperatorJet (dressedKinematicPoint event kt.1) reader
        (voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial kt.1) imaginary) kt.2).value) := by
  have resolvent := (actualJointResolvent_continuous event.frame event.energy event.nonreal).comp
    (show Continuous (fun kt : PhysicalMomentum × ℝ =>event.momentum-kt.1) from continuous_const.sub continuous_fst)
  have initial : Continuous (fun kt : PhysicalMomentum × ℝ =>
      jointResolvent (event.momentum-kt.1) event.frame event.energy 0*
        rawReader reader event.momentum event.frame 0*jointResolvent event.momentum event.frame event.energy 0) :=
    (resolvent.mul continuous_const).mul continuous_const
  have left := (time_left_continuous event).comp (continuous_fst.prodMk continuous_snd.neg)
  have right := (actualJointTime_continuous event.frame).comp
    (show Continuous (fun kt : PhysicalMomentum × ℝ =>(event.momentum,kt.2)) from continuous_const.prodMk continuous_snd)
  have middle := middle_continuous event reader imaginary
  have correction := ((fderiv ℝ (noetherReader reader event.momentum event.frame) 0)-
    (fderiv ℝ (rawReader reader event.momentum event.frame) 0)).continuous.comp
      (voltage_value_continuous imaginary)
  simp only [noetherHistoryOperatorJet_value,historyOperator,rawInitial,dressedKinematicPoint,
    ←sub_eq_add_neg,noether_contact_linear,raw_contact_linear]
  exact (((primal_continuous event imaginary) |> fun primal =>
    (((dual_continuous event imaginary).mul initial).mul right).add ((left.mul middle).mul right) |>.add
      ((left.mul initial).mul primal))).add
    ((((left.mul resolvent).mul correction).mul continuous_const).mul right)

/-- This is the original unit-minus-background observer; the old prepared-pair reader does not enter. -/
theorem dressed_voltage_transfer_time_continuous (event : DressedEvent) (imaginary : Bool) (i : Fin 289) :
    Continuous (fun kt : PhysicalMomentum × ℝ =>
      (dressedNoetherJet event kt.1 (voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial kt.1) imaginary) kt.2 i).value) :=
  (dressedEulerObserver event).continuous.comp
    (dressed_voltage_operator_transfer_continuous event (fieldUnit i) imaginary)

/-- Transfer, both time-ordered legs and the Laplace frequency share a single finite-window integral. -/
theorem dressed_voltage_transfer_spectral_continuous (event : DressedEvent) (T : ℝ) :
    Continuous (fun kz : PhysicalMomentum  ×  ℂ =>dressedVoltageForcing event kz.1 kz.2 T) := by
  have quadrature (imaginary : Bool) : Continuous (fun kz : PhysicalMomentum  ×  ℂ =>
      dressedNoetherForcing event kz.1 (voltageNativeTimeJet (PreparationVacuumPhysicalFeedback.physicalSpatial kz.1) imaginary) kz.2 T) := by
    apply continuous_pi
    intro i
    have current := (dressed_voltage_transfer_time_continuous event imaginary i).comp
      (show Continuous (fun x : (PhysicalMomentum × ℂ) × ℝ =>(x.1.1,x.2)) from
        continuous_fst.fst.prodMk continuous_snd)
    have weight : Continuous (fun x : (PhysicalMomentum × ℂ) × ℝ =>laplaceWeight x.1.2 x.2) := by
      unfold laplaceWeight
      fun_prop
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (weight.mul current) 0 T
  unfold dressedVoltageForcing
  exact (quadrature false).add ((quadrature true).const_smul Complex.I)

/-- A single source-generated neighborhood bounds every transfer direction and spectral approach. -/
theorem dressed_voltage_transfer_bound (event : DressedEvent) (T : ℝ) :
    ∃radius : ℝ, 0<radius ∧ ∀(k : PhysicalMomentum) (z : ℂ), ‖(k,z)‖<radius →
      ‖dressedVoltageForcing event k z T‖ ≤ ‖dressedVoltageForcing event 0 0 T‖+1 := by
  have near := (dressed_voltage_transfer_spectral_continuous event T).tendsto (0,0) |>.eventually
    (eventually_norm_sub_lt (dressedVoltageForcing event 0 0 T) (by norm_num : (0:ℝ)<1))
  obtain ⟨radius,positive,bound⟩ := Metric.eventually_nhds_iff.mp near
  refine ⟨radius,positive,?_⟩
  intro k z small
  have hdist : dist (k,z) (0,0)<radius := by
    rw [show ((0,0):PhysicalMomentum × ℂ)=0 from rfl,dist_zero_right]
    exact small
  have delta := @bound (k,z) hdist
  exact (norm_le_norm_sub_add (dressedVoltageForcing event k z T)
    (dressedVoltageForcing event 0 0 T)).trans (by linarith)

/-- The moving current is generated from the same actual transfer and its source sheet frequency. -/
def dressedSoftCurrent (event : DressedEvent) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (T : ℝ) (e : scaleDomain) : Fin 289→ℂ :=
  dressedGaugeCurrent event e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n T

theorem dressed_soft_current_tendsto (event : DressedEvent) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (T : ℝ) :
    Tendsto (dressedSoftCurrent event branch n unit T) scaleApproach
      (𝓝 (dressedVoltageForcing event 0 0 T)) := by
  have square := scaleVal_tendsto.pow 2
  have transfer : Tendsto (fun e : scaleDomain=>(e.val^2:ℝ) • n) scaleApproach (𝓝 (0:PhysicalMomentum)) := by
    simpa only [zero_pow (by omega : 2≠0),zero_smul] using square.smul_const n
  have omega : Tendsto (fun e : scaleDomain=>sourceFrequency e.val (sourceSheet branch n unit e.val))
      scaleApproach (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_apply,sourceFrequency,zero_pow (by omega : 2≠0),zero_mul] using
      square.mul ((sourceSheet_tendsto branch n unit).comp scaleVal_tendsto)
  have frequency : Tendsto (fun e : scaleDomain=>-Complex.I*
      (sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ)) scaleApproach (𝓝 (0:ℂ)) := by
    simpa only [Function.comp_apply,Complex.ofReal_zero,mul_zero] using
      (Complex.continuous_ofReal.tendsto 0 |>.comp omega).const_mul (-Complex.I)
  have result := (dressed_voltage_transfer_spectral_continuous event T).tendsto (0,0) |>.comp
    (transfer.prodMk_nhds frequency)
  change Tendsto (fun e=>dressedSoftCurrent event branch n unit T e) scaleApproach _
  simpa only [Function.comp_def,dressedSoftCurrent,dressedGaugeCurrent] using result

/-- The whole mixed residue consumes the generated moving family, retaining every field-current component. -/
theorem dressed_soft_whole_pole (event : DressedEvent) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (T : ℝ) :
    Tendsto (fun e : scaleDomain=>(2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ)) •
      dressedGaugePole event e.val (sourceSheet branch n unit e.val) n T) scaleApproach
      (𝓝 (leadingNativeResponse branch (dressedVoltageForcing event 0 0 T))) := by
  simpa only [dressedGaugePole,dressedSoftCurrent] using
    em_moving_whole_response_ir branch n unit _ _ (dressed_soft_current_tendsto event branch n unit T)

/-- Both generated sheets return the full four-component EM restriction of that same moving actual current. -/
theorem dressed_soft_em_pole (event : DressedEvent) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (T : ℝ) (mu : Fin 4) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ))*
      (emInsertion.transpose *ᵥ dressedGaugePole event e.val (sourceSheet branch n unit e.val) n T) mu)
      scaleApproach (𝓝 (sourceCurvatureEmitterInput (dressedVoltageForcing event 0 0 T) (residueIndex branch)*
        emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu (fiveIndex (residueIndex branch))*
        (softCoefficient branch:ℂ))) := by
  simpa only [dressedGaugePole,dressedSoftCurrent] using
    em_moving_current_response_ir branch n unit _ _ (dressed_soft_current_tendsto event branch n unit T) mu

/-- All twelve gauge directions and all six electric/magnetic pairs read the same actual moving pole. -/
theorem dressed_soft_full_curvature_pole (event : DressedEvent) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (T : ℝ) (pair : Fin 6) (a : Fin 12) :
    Tendsto (fun e : scaleDomain=>(2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ))*
      fullGaugeCurvature (frequencyRay e.val (sourceSheet branch n unit e.val) n)
        (dressedGaugePole event e.val (sourceSheet branch n unit e.val) n T) pair a)
      scaleApproach (𝓝 (fullGaugeCurvature 0
        (leadingNativeResponse branch (dressedVoltageForcing event 0 0 T)) pair a)) := by
  have result := (full_gauge_curvature_continuous pair a).tendsto
    (0,leadingNativeResponse branch (dressedVoltageForcing event 0 0 T)) |>.comp
      ((sourceRay_soft_limit branch n unit).prodMk_nhds (dressed_soft_whole_pole event branch n unit T))
  apply result.congr'
  filter_upwards [] with e
  exact (fullGaugeRead _ pair a).map_smul _ _

end LowEnergy.GaussComposite.ActualEMDressedTransferIR
