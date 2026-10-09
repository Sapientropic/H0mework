import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualMasslessStaticPair

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualMasslessFullKernel
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback
open PreparationVacuumRawJointFeedback PreparationVacuumRestModeCoupling
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalActualLegNormalization
open PreparationVacuumFullPoleContinuation PreparationVacuumActionFieldLift
open PreparationVacuumGaugeSourceInjection PreparationVacuumMixedFieldReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumStaticPoleResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationPhysicalStaticSpatialCouplingReturn ActualEMResponseSplit
open ActualEMObservable ActualElectronOwnerTest ActualMasslessCurrent ActualMasslessStaticPair
open MeasureTheory Filter
open scoped BigOperators Matrix Topology Interval
attribute [local irreducible] actualJointKernel physicalTime jointResolvent rawReader sourceModeReader

/-- The entire actual five-factor kernel, before any base/upper material restriction. -/
def actualMasslessFullKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (age : ℝ) : H→L[ℂ]H :=
  physicalTime pL q.F (-age) 0*jointResolvent pL q.F q.z 0*sourceModeReader q.F*
    jointResolvent pR q.F q.w 0*physicalTime pR q.F age 0

/-- The generated long-range source reads the original two slots in the same full material event. -/
theorem actual_massless_full_kernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (age : ℝ) :
    actualJointKernel q pL pR age 21-actualJointKernel q pL pR age 34=
      actualMasslessFullKernel q pL pR age := by
  unfold actualJointKernel actualMasslessFullKernel
  rw [←sub_mul,←sub_mul,←mul_sub]
  rw [show fieldUnit 21=gaugeField 1 0 from rfl,show fieldUnit 34=gaugeField 2 1 from rfl,
    sourceModeReader_generated]

private theorem fieldKernel_single (q : PhysicalResponsePoint) (lambda : ℂ) (T : ℝ) (i : Fin 289) :
    actualElectronFieldKernel q lambda T (Pi.single i 1)=
      ∫t in (0:ℝ)..T,laplaceWeight lambda t • actualJointKernel q 0 0 t i := by
  simp only [actualElectronFieldKernel,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,Pi.single_apply,ite_smul,one_smul,zero_smul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]

private theorem weighted_kernel_integrable (q : PhysicalResponsePoint) (lambda : ℂ) (T : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (i : Fin 289) :
    IntervalIntegrable (fun age : ℝ=>laplaceWeight lambda age • actualJointKernel q 0 0 age i)
      volume 0 T := by
  have argument : Continuous (fun age : ℝ=>((0:PhysicalMomentum),(0:PhysicalMomentum),age)) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have kernel:=(actualJointKernel_continuous q i hz hw).comp argument
  have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
  exact (weight.smul kernel).intervalIntegrable _ _

/-- Full filters, independently normalized actual dual/primal, and the original finite window generate the coupling. -/
theorem actual_unit_massless_full_kernel_read (q : PhysicalResponsePoint) (sideL sideR : Fin 2)
    (lambda : ℂ) (T : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    actualUnitMasslessWeight q sideL sideR lambda T=
      (3/10:ℂ)*rootTwo*actualElectronOperatorTest q sideL sideR
        (∫age in (0:ℝ)..T,laplaceWeight lambda age • actualMasslessFullKernel q 0 0 age) := by
  unfold actualUnitMasslessWeight emUnitSourceCurrent emUnitSourceTest
  simp only [ContinuousLinearMap.comp_apply,fieldKernel_single]
  rw [←map_sub,←intervalIntegral.integral_sub
    (weighted_kernel_integrable q lambda T hz hw 21) (weighted_kernel_integrable q lambda T hz hw 34)]
  apply congrArg (fun A : H→L[ℂ]H=>(3/10:ℂ)*rootTwo*actualElectronOperatorTest q sideL sideR A)
  apply intervalIntegral.integral_congr
  intro age _
  dsimp only
  rw [←actual_massless_full_kernel q 0 0 age]
  exact (smul_sub (laplaceWeight lambda age) (actualJointKernel q 0 0 age 21)
    (actualJointKernel q 0 0 age 34)).symm

/-- The original actual dual/primal and full five factors are the same source event used by the static pair. -/
theorem actual_unit_massless_original_leg_read (q : PhysicalResponsePoint) (sideL sideR : Fin 2)
    (lambda : ℂ) (T : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    actualUnitMasslessWeight q sideL sideR lambda T=
      -(3/10:ℂ)*rootTwo*sourceActualUnitLegRead q sideL 0 sideR 0
        (∫age in (0:ℝ)..T,laplaceWeight lambda age • actualMasslessFullKernel q 0 0 age) := by
  rw [actual_unit_massless_full_kernel_read q sideL sideR lambda T hz hw,
    actualElectronOperatorTest_actual]
  ring

/-- No caller chooses the two scalar couplings: both are generated by the original actual full-kernel event. -/
theorem actual_unit_full_green_kernel_limit (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (branch : Fin 2) (qd qs : PhysicalResponsePoint) (dL dR sL sR : Fin 2)
    (lambda mu : ℂ) (T S : ℝ) (hzd : qd.z.im≠0) (hwd : qd.w.im≠0)
    (hzs : qs.z.im≠0) (hws : qs.w.im≠0) :
    Tendsto (fun kappa : staticDomain=>(kappa.val:ℂ)^2*
      emCurrentObservation (sourceGreen (sourceSpatialStaticRegularPoint n unit kappa))
        (emUnitDetectorCovector branch qd dL dR lambda T) (emUnitSourceCurrent qs sL sR mu S))
      staticApproach
      (𝓝 (actualStaticPairSeed*
        ((3/10:ℂ)*rootTwo*actualElectronOperatorTest qd dL dR
          (∫age in (0:ℝ)..T,laplaceWeight lambda age • actualMasslessFullKernel qd 0 0 age))*
        ((3/10:ℂ)*rootTwo*actualElectronOperatorTest qs sL sR
          (∫age in (0:ℝ)..S,laplaceWeight mu age • actualMasslessFullKernel qs 0 0 age))/
          (((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)))) := by
  have result:=actual_unit_full_green_limit n unit branch qd qs dL dR sL sR lambda mu T S
  rw [actual_unit_massless_full_kernel_read qd dL dR lambda T hzd hwd,
    actual_unit_massless_full_kernel_read qs sL sR mu S hzs hws] at result
  exact result

end LowEnergy.GaussComposite.ActualMasslessFullKernel
