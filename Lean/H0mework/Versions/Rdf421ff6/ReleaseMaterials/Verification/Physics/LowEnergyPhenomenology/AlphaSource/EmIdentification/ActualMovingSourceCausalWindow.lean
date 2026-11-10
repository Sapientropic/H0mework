import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualMovingSourcePhysicalPartition
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualQuantumBinaryReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualMovingSourceLight
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource SourceQuantumFockGauge
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open ActualSourcePreparationBridge ActualSourceLightCircuit
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumJointFieldResponse
open PreparationVacuumRawJointFeedback PreparationVacuumNoetherChart PreparationVacuumNoetherOrdinaryWard
open ActualDressedFullCoulomb ActualDressedNoether ActualElectronWholeNoetherObserver
open ActualElectronFullNoetherMixedSoft ActualCompositeFieldCurrent
open ActualElectronQuarterSourceMatching ActualDressedFiniteStaticRead
open PreparationVacuumPhysicalHalfAxis PreparationVacuumSourcePreparedResponse
open ActualMixedNoetherTimePriceOwn ActualDressedSylvester
open scoped Topology InnerProductSpace Matrix Matrix.Norms.L2Operator BigOperators
local instance instDecidableEqMode_actualMovingSourceCausalWindow : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local irreducible] jointResolvent jointCurrent physicalTime timeSlope noetherReader noetherReaderContact
  actualMovingNoetherReader actualMovingNoetherReaderContact actualMovingHeavyNoetherReader
  actualMovingHeavyNoetherReaderContact projectedNoetherReader projectedNoetherReaderContact
  actualPhysicalEulerObserver dressedEulerObserver
  actualMovingSourceVariation actualMovingHeavySourceVariation actualFullNoetherVariation
  originalQuantumBinaryWindow finiteConstantFieldSlope dressedStaticPolarization
  sourceProjectedVariation sourceRestCrossOutsideMap sourceProjectedWindowOperator sourceProjectedPhysicalWindow
  PhysicalN3CausalWindow.physicalN3ResponseWindowOperator PhysicalN3CausalWindow.physicalN3ResponseWindow

open ActualEMJointCurrentMomentum ActualElectronPhysicalJointInverse ActualElectronWholeChargeSoft
open PreparationVacuumFullPoleContinuation PreparationVacuumFieldPerturbation.Blocks
open PreparationVacuumGaugeSourceInjection PhysicalN3CausalWindow ActualMixedNoetherTimePriceOwn
open MeasureTheory intervalIntegral
local instance movingWindowReal : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance movingWindowRational : NormedAlgebra ℚ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℚ ℂ _
theorem actual_moving_source_variation_joint (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (reader force : Field289) :
    Continuous (fun kt : PhysicalMomentum×ℝ=>actualMovingSourceVariation pL pR reference event (-kt.1) reader force kt.2) := by
  have momentum : Continuous (fun kt : PhysicalMomentum×ℝ=>event.momentum+kt.1):=
    (continuous_const (y:=event.momentum)).add continuous_fst
  have leftpair : Continuous (fun kt : PhysicalMomentum×ℝ=>(event.momentum+kt.1,-kt.2)):=by fun_prop
  have tl:=(actualJointTime_continuous event.frame).comp leftpair
  have l:=(actual_electron_physical_resolvent_continuous event.frame event.energy event.nonreal).comp momentum
  have dtl:=(physical_n3_time_slope_joint event.frame force).comp leftpair
  have current:=((joint_current_momentum_continuous event.frame event.energy).comp momentum).clm_apply
    (continuous_const (y:=force))
  have dl:=((l.mul current).mul l).neg
  have dJ : Continuous (fun _ : PhysicalMomentum×ℝ=>
    actualMovingNoetherReaderContact pL pR reference reader force event.momentum event.frame):=continuous_const
  have J : Continuous (fun _ : PhysicalMomentum×ℝ=>
    actualMovingNoetherReader pL pR reference reader event.momentum event.frame 0):=continuous_const
  have R : Continuous (fun _ : PhysicalMomentum×ℝ=>jointResolvent event.momentum event.frame event.energy 0):=continuous_const
  have dR : Continuous (fun _ : PhysicalMomentum×ℝ=>-(jointResolvent event.momentum event.frame event.energy 0*
    jointCurrent event.momentum event.frame event.energy 0 force*jointResolvent event.momentum event.frame event.energy 0)):=continuous_const
  have rightpair : Continuous (fun kt : PhysicalMomentum×ℝ=>(event.momentum,kt.2)):=by fun_prop
  have TR:=(actualJointTime_continuous event.frame).comp rightpair
  have dTR:=(physical_n3_time_slope_joint event.frame force).comp rightpair
  have generated:=(((((dtl.mul l).add (tl.mul dl)).mul J).add ((tl.mul l).mul dJ)).mul R |>.add
    (((tl.mul l).mul J).mul dR)).mul TR |>.add ((((tl.mul l).mul J).mul R).mul dTR)
  simpa only [actualMovingSourceVariation,sub_neg_eq_add,Function.comp_def,Pi.mul_apply,Pi.add_apply,
    Pi.neg_apply] using! generated


private theorem isolate_generated_heavy {E : Type*} [AddCommGroup E] (A L B C : E)
    (partition : A=L+B+C) : B=(A-C)-L:=by
  rw [partition]
  abel

/-- Regularity is inherited from the exact source partition; heavy remains its generated I-P current. -/
theorem actual_moving_heavy_variation_joint (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (reader force : Field289) :
    Continuous (fun kt : PhysicalMomentum×ℝ=>actualMovingHeavySourceVariation pL pR reference event (-kt.1) reader force kt.2):=by
  have full:=physical_n3_variation_joint event reader force
  have outside:=source_projected_variation_joint sourceRestCrossOutsideMap event reader force
  have light:=actual_moving_source_variation_joint pL pR reference event reader force
  apply ((full.sub outside).sub light).congr
  intro kt
  exact (isolate_generated_heavy _ _ _ _
    (actual_full_noether_moving_source_partition pL pR reference event (-kt.1) reader force kt.2)).symm

def actualMovingWindowOperator (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289) : H→L[ℂ]H:=
  ∫age in (0:ℝ)..T,laplaceWeight lambda age • actualMovingSourceVariation pL pR reference event (-k) reader force age

def actualMovingHeavyWindowOperator (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289) : H→L[ℂ]H:=
  ∫age in (0:ℝ)..T,laplaceWeight lambda age • actualMovingHeavySourceVariation pL pR reference event (-k) reader force age

attribute [local irreducible] actualMovingWindowOperator actualMovingHeavyWindowOperator

private theorem weighted_window_integrable (lambda : ℂ) (T : ℝ) (f : ℝ→H→L[ℂ]H) (hf : Continuous f) :
    IntervalIntegrable (fun age=>laplaceWeight lambda age • f age) volume 0 T:=by
  have weight : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
  exact (weight.smul hf).intervalIntegrable (μ:=volume) 0 T

private theorem moving_age_continuous (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) :
    Continuous (actualMovingSourceVariation pL pR reference event transfer reader force):=by
  simpa only [Function.comp_def,neg_neg,id_eq] using
    (actual_moving_source_variation_joint pL pR reference event reader force).comp
      ((continuous_const (y:= -transfer)).prodMk continuous_id)

private theorem heavy_age_continuous (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) :
    Continuous (actualMovingHeavySourceVariation pL pR reference event transfer reader force):=by
  simpa only [Function.comp_def,neg_neg,id_eq] using
    (actual_moving_heavy_variation_joint pL pR reference event reader force).comp
      ((continuous_const (y:= -transfer)).prodMk continuous_id)

private theorem outside_age_continuous (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) :
    Continuous (sourceProjectedVariation sourceRestCrossOutsideMap event transfer reader force):=by
  simpa only [Function.comp_def,neg_neg,id_eq] using
    (source_projected_variation_joint sourceRestCrossOutsideMap event reader force).comp
      ((continuous_const (y:= -transfer)).prodMk continuous_id)

/-- The unchanged full causal operator integrates all three generated source arms. -/
theorem actual_physical_n3_window_operator_moving_partition (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289) :
    physicalN3ResponseWindowOperator event k lambda T reader force=
      actualMovingWindowOperator pL pR reference event k lambda T reader force+
      actualMovingHeavyWindowOperator pL pR reference event k lambda T reader force+
      sourceProjectedWindowOperator sourceRestCrossOutsideMap event k lambda T reader force:=by
  have light:=weighted_window_integrable lambda T _ (moving_age_continuous pL pR reference event (-k) reader force)
  have heavy:=weighted_window_integrable lambda T _ (heavy_age_continuous pL pR reference event (-k) reader force)
  have outside:=weighted_window_integrable lambda T _ (outside_age_continuous event (-k) reader force)
  unfold physicalN3ResponseWindowOperator actualMovingWindowOperator actualMovingHeavyWindowOperator sourceProjectedWindowOperator
  have partition : (∫age in (0:ℝ)..T,laplaceWeight lambda age • actualFullNoetherVariation event (-k) reader force age)=
      ∫age in (0:ℝ)..T,
        (laplaceWeight lambda age • actualMovingSourceVariation pL pR reference event (-k) reader force age+
          laplaceWeight lambda age • actualMovingHeavySourceVariation pL pR reference event (-k) reader force age)+
        laplaceWeight lambda age • sourceProjectedVariation sourceRestCrossOutsideMap event (-k) reader force age:=by
    apply intervalIntegral.integral_congr
    intro age _
    exact (congrArg (fun A : H→L[ℂ]H=>laplaceWeight lambda age • A)
      (actual_full_noether_moving_source_partition pL pR reference event (-k) reader force age)).trans
        ((smul_add _ _ _).trans (congrArg (fun A : H→L[ℂ]H=>A+
          laplaceWeight lambda age • sourceProjectedVariation sourceRestCrossOutsideMap event (-k) reader force age)
          (smul_add _ _ _)))
  exact partition.trans ((intervalIntegral.integral_add (light.add heavy) outside).trans
    (congrArg (fun A : H→L[ℂ]H=>A+∫age in (0:ℝ)..T,laplaceWeight lambda age •
      sourceProjectedVariation sourceRestCrossOutsideMap event (-k) reader force age)
      (intervalIntegral.integral_add light heavy)))

/-- The actual physical N3 observer reads the same complete finite operator. -/
theorem actual_physical_n3_window_moving_partition (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (leg : CompositeLeg) (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289) :
    physicalN3ResponseWindow event leg k lambda T reader force=
      actualPhysicalEulerObserver event leg (actualMovingWindowOperator pL pR reference event k lambda T reader force)+
      actualPhysicalEulerObserver event leg (actualMovingHeavyWindowOperator pL pR reference event k lambda T reader force)+
      sourceProjectedPhysicalWindow sourceRestCrossOutsideMap event leg k lambda T reader force:=by
  unfold physicalN3ResponseWindow sourceProjectedPhysicalWindow
  simpa only [map_add] using
    congrArg (actualPhysicalEulerObserver event leg)
      (actual_physical_n3_window_operator_moving_partition pL pR reference event k lambda T reader force)

def actualMovingOriginalWindow (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (i j : Fin 289) : ℂ:=
  ∫age in (0:ℝ)..T,laplaceWeight lambda age*
    actualMovingOriginalResponse pL pR reference event transfer (fieldUnit i) (fieldUnit j) age

def actualMovingHeavyOriginalWindow (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (i j : Fin 289) : ℂ:=
  ∫age in (0:ℝ)..T,laplaceWeight lambda age*
    dressedEulerObserver event (actualMovingHeavySourceVariation pL pR reference event transfer (fieldUnit i) (fieldUnit j) age)

def actualCrossOutsideOriginalWindow (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (i j : Fin 289) : ℂ:=
  ∫age in (0:ℝ)..T,laplaceWeight lambda age*
    dressedEulerObserver event (sourceProjectedVariation sourceRestCrossOutsideMap event transfer (fieldUnit i) (fieldUnit j) age)

attribute [local irreducible] actualMovingOriginalWindow actualMovingHeavyOriginalWindow actualCrossOutsideOriginalWindow

private theorem scalar_window_integrable (event : DressedEvent) (lambda : ℂ) (T : ℝ)
    (f : ℝ→H→L[ℂ]H) (hf : Continuous f) :
    IntervalIntegrable (fun age=>laplaceWeight lambda age*dressedEulerObserver event (f age)) volume 0 T:=by
  have weight : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
  exact (weight.mul ((dressedEulerObserver event).continuous.comp hf)).intervalIntegrable (μ:=volume) 0 T

/-- Both old preparation arms, the original horizon, and the full source operator are preserved. -/
theorem actual_original_quantum_binary_moving_partition (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (bits : ℕ) (i j : Fin 289) :
    originalQuantumBinaryWindow event transfer lambda bits i j=
      actualMovingOriginalWindow pL pR reference event transfer lambda (originalQuantumHorizon lambda.re bits) i j+
      actualMovingHeavyOriginalWindow pL pR reference event transfer lambda (originalQuantumHorizon lambda.re bits) i j+
      actualCrossOutsideOriginalWindow event transfer lambda (originalQuantumHorizon lambda.re bits) i j:=by
  have light:=scalar_window_integrable event lambda (originalQuantumHorizon lambda.re bits) _
    (moving_age_continuous pL pR reference event transfer (fieldUnit i) (fieldUnit j))
  have heavy:=scalar_window_integrable event lambda (originalQuantumHorizon lambda.re bits) _
    (heavy_age_continuous pL pR reference event transfer (fieldUnit i) (fieldUnit j))
  have outside:=scalar_window_integrable event lambda (originalQuantumHorizon lambda.re bits) _
    (outside_age_continuous event transfer (fieldUnit i) (fieldUnit j))
  unfold originalQuantumBinaryWindow originalFullQuantumWindow dressedNoetherForcing
    actualMovingOriginalWindow actualMovingHeavyOriginalWindow actualCrossOutsideOriginalWindow actualMovingOriginalResponse
  simp_rw [←finite_constant_field_slope_actual,actual_original_finite_slope_moving_partition pL pR reference,mul_add]
  exact (intervalIntegral.integral_add (light.add heavy) outside).trans
    (congrArg (fun z : ℂ=>z+∫age in (0:ℝ)..originalQuantumHorizon lambda.re bits,laplaceWeight lambda age*
        dressedEulerObserver event (sourceProjectedVariation sourceRestCrossOutsideMap event transfer (fieldUnit i) (fieldUnit j) age))
      (intervalIntegral.integral_add light heavy))

/-- The infinite original read is returned through the actual moving light window and generated heavy/cross/outside, with its paid full-source tail. -/
theorem actual_moving_source_light_window_error (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ)
    (positive : 0<lambda.re) (small : lambda.re≤2) (bits : ℕ) (i j : Fin 289) :
    ‖dressedStaticPolarization event transfer lambda i j-
      actualMovingOriginalWindow pL pR reference event transfer lambda (originalQuantumHorizon lambda.re bits) i j‖≤
      (896*sourceCompleteCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j)/lambda.re^4)*(1/2:ℝ)^bits+
      ‖actualMovingHeavyOriginalWindow pL pR reference event transfer lambda (originalQuantumHorizon lambda.re bits) i j+
        actualCrossOutsideOriginalWindow event transfer lambda (originalQuantumHorizon lambda.re bits) i j‖:=by
  have partition:=actual_original_quantum_binary_moving_partition pL pR reference event transfer lambda bits i j
  have full:=actualFullQuantum_binary_source_error event transfer lambda positive small bits i j
  have scalar (A L B C : ℂ) (same : B=L+C) : ‖A-L‖≤‖A-B‖+‖C‖:=by
    have identity : A-L=(A-B)+C:=by rw [same];ring
    rw [identity]
    exact norm_add_le _ _
  exact (scalar _ _ _ _ (partition.trans (add_assoc _ _ _))).trans (add_le_add full le_rfl)

end LowEnergy.GaussComposite.ActualMovingSourceLight
