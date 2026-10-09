import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceN1Prepared

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalN1WardCollapse
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection
  rawReader jointResolvent jointGenerator

open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set


open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential

open PreparationVacuumOriginalGreenFeedback

open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology

open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _

open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion

open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
local instance : NormedAlgebra ℝ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] noetherReader noetherForm sourceApprox sourceTestApprox

open PreparationVacuumPhysicalColorWard
local instance : NormedAlgebra ℚ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] sourcePolePrepared sourceExcitedProjection

def sourceN1Core (f : QuantumTest) : QuantumTest :=
  GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel f+GaussCoreLabel.project sourceExcitedLabel f

theorem originalY_sourceZero_range (f : QuantumTest) :
    GaussCoreLabel.project sourceExcitedLabel (GaussYukawaOperator.originalAction
      (GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel f))=
        GaussYukawaOperator.originalAction (GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel f) := by
  apply DFunLike.ext
  intro z
  exact sourceMap_N1G0_range _ _

theorem originalY_sourceOne_zero (f : QuantumTest) :
    GaussYukawaOperator.originalAction (GaussCoreLabel.project sourceExcitedLabel f)=0 := by
  apply DFunLike.ext
  intro z
  exact sourceMap_N1G1_zero _ _

theorem normalCharge_originalY_zero (a : Fin 12) (f : QuantumTest) :
    normalChargeCore a (GaussYukawaOperator.originalAction
      (GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel f))=0 := by
  exact (congrArg (normalChargeCore a) (originalY_sourceZero_range f)).symm.trans
    (sourceGradeOne_normalCharge_zero a _)

theorem normalCharge_fullSource_N1_zero (p : PhysicalMomentum) (a : Fin 12) (f : QuantumTest) :
    normalChargeCore a (fullSourceAction p (sourceN1Core f))=0 := by
  have h0:=CanonicalPhysicalSpatial.physicalAction_blocks p CanonicalGradedCurrent.sourceLabel f
  have h1:=CanonicalPhysicalSpatial.physicalAction_blocks p sourceExcitedLabel f
  unfold sourceN1Core fullSourceAction
  simp only [LinearMap.add_apply,map_add]
  rw [←h0,←h1,sourceGradeZero_normalCharge_zero,sourceGradeOne_normalCharge_zero,
    normalCharge_originalY_zero,originalY_sourceOne_zero,map_zero]
  simp only [zero_add]

theorem sourceActualN1Primal_fullSource_normal_zero (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (actualP : PhysicalMomentum) (a : Fin 12) :
    normalChargeCore a (fullSourceAction actualP
      (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))=0 := by
  have fixed:=sourceActualN1Primal_core q p state z t nonreal
  change sourceN1Core (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=
    sourceTestApprox q.F (sourceActualN1Primal q p state z t) at fixed
  exact (congrArg (fun f : QuantumTest=>normalChargeCore a (fullSourceAction actualP f)) fixed).symm.trans
    (normalCharge_fullSource_N1_zero actualP a _)

theorem sourceActualN1Primal_normalTorque_zero (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (actualP transfer : PhysicalMomentum) (a : Fin 12) :
    normalActionTorque actualP transfer a (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=0 := by
  unfold normalActionTorque
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,sourceActualN1Primal_normalCharge_zero q p state z t nonreal,
    map_zero,sourceActualN1Primal_fullSource_normal_zero q p state z t nonreal,sub_zero]

private theorem pairCurrent_label_zero (k : PhysicalMomentum) (a : NativeLie) (g : Label)
    (one : g.1.val=1) (f : QuantumTest) :
    pairCurrent k a (GaussCoreLabel.project g f)=0 := by
  apply DFunLike.ext
  intro z
  rw [pairCurrent_apply,GaussCoreLabel.project_apply]
  exact congrArg (fun A : FockFiber→L[ℂ] FockFiber=>A (f z))
    (sourceNumberOne_pairFiber_zero g one (momentumMatrix z k) (chargeMatrix a))

theorem sourceActualN1Primal_pairCurrent_zero (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (k : PhysicalMomentum) (a : NativeLie) :
    pairCurrent k a (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=0 := by
  have fixed:=sourceActualN1Primal_core q p state z t nonreal
  have h:=congrArg (pairCurrent k a) fixed
  simp only [map_add,pairCurrent_label_zero k a CanonicalGradedCurrent.sourceLabel rfl,
    pairCurrent_label_zero k a sourceExcitedLabel rfl,zero_add] at h
  exact h.symm

def sourceN1WardCore (k : PhysicalMomentum) (a : NativeLie) : QuantumTest→ₗ[ℂ] QuantumTest :=
  CanonicalPhysicalWardCore.configurationTorque a+CanonicalPhysicalWardCore.currentAction k a+yukawaTorque a

theorem sourceActualN1Primal_weightedWard (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (actualP k : PhysicalMomentum) (a : Fin 12) :
    weightedWardCore actualP k a (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=
      weightCore (sourceN1WardCore k (originalUnit a) (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))+
        weightActionTorque (actualP+k) (chargeAction (originalUnit a)
          (sourceTestApprox q.F (sourceActualN1Primal q p state z t))) := by
  unfold weightedWardCore sourceN1WardCore wardCore
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.comp_apply,
    sourceActualN1Primal_normalTorque_zero q p state z t nonreal,
    sourceActualN1Primal_pairCurrent_zero q p state z t nonreal,add_zero,sub_zero]

private theorem testApprox_normal_zero (F : GaussUnitaryHistory.Index) (y : H)
    (fixed : sourceN1Projection y=y) (a : Fin 12) : normalChargeCore a (sourceTestApprox F y)=0 := by
  have h:=congrArg (sourceTestApprox F) fixed
  unfold sourceN1Projection at h
  rw [add_apply,sourceTestApprox_add] at h
  simp only [sourceProjection,sourceExcitedProjection,sourceTestApprox_projection] at h
  have zero:=congrArg (normalChargeCore a) h
  simp only [map_add,sourceGradeZero_normalCharge_zero,sourceGradeOne_normalCharge_zero,zero_add] at zero
  exact zero.symm

theorem sourceActualN1Primal_rightDefect_normal_zero (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (actualP : PhysicalMomentum) (a : Fin 12) :
    normalChargeCore a (rightCompressionDefect actualP q.F (sourceActualN1Primal q p state z t)+
      rightUncutDefect actualP q.F (sourceActualN1Primal q p state z t))=0 := by
  let y:=sourceActualN1Primal q p state z t
  have fixed:=sourceActualN1Primal_generated q p state z t nonreal
  change sourceN1Projection y=y at fixed
  have h:=congrArg (fun A : H→L[ℂ] H=>A y) (actualGenerator_sourceN1_range actualP q.F)
  simp only [mul_apply_eq_comp,fixed] at h
  have zero:=testApprox_normal_zero q.F (sourceHamiltonian actualP q.F y) h a
  have action:=congrArg (normalChargeCore a) (rightAction_source actualP q.F y)
  have full : normalChargeCore a (fullSourceAction actualP (sourceTestApprox q.F y))=0:=
    sourceActualN1Primal_fullSource_normal_zero q p state z t nonreal actualP a
  simp only [map_add] at action
  rw [zero,full,zero_add] at action
  simpa only [map_add] using action.symm

def sourceN1GaugeWardReturn (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (a : Fin 12) (y : H) : H :=
  let f:=sourceTestApprox q.F y
  let d:=rightCompressionDefect pR q.F y+rightUncutDefect pR q.F y
  sourceApprox q.F (embed (weightCore (sourceN1WardCore (pL-pR) (originalUnit a) f)+
    weightActionTorque pL (chargeAction (originalUnit a) f)))+
    leftCompressionDefect pL q.F (weightCore (chargeAction (originalUnit a) f))+
    leftUncutDefect pL q.F (weightCore (chargeAction (originalUnit a) f))-
    sourceApprox q.F (embed (weightCore (chargeAction (originalUnit a) d)))

def sourceN1ColorWardReturn (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (y : H) : H :=
  (1/2 : ℝ) • (sourceN1GaugeWardReturn q pL pR 6 y-sourceN1GaugeWardReturn q pL pR 7 y)

private theorem replace_three {A B : Type*} (F : A→A→A→B) {w w' r r' d d' : A}
    (hw : w=w') (hr : r=r') (hd : d=d') : F w r d=F w' r' d' := by
  cases hw
  cases hr
  cases hd
  rfl

private theorem actualGaugeWard_return_N1 (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (a : Fin 12) :
    let y:=sourceActualN1Primal q pR state z t
    sourceApprox q.F (embed (weightedWardCore pR (pL-pR) a (sourceTestApprox q.F y)))+
      leftCompressionDefect pL q.F (rawChargeCore a (sourceTestApprox q.F y))+
      leftUncutDefect pL q.F (rawChargeCore a (sourceTestApprox q.F y))-
      sourceApprox q.F (embed (rawChargeCore a (rightCompressionDefect pR q.F y+rightUncutDefect pR q.F y)))=
        sourceN1GaugeWardReturn q pL pR a y := by
  let y:=sourceActualN1Primal q pR state z t
  have ward:=sourceActualN1Primal_weightedWard q pR state z t nonreal pR (pL-pR) a
  have momentum : pR+(pL-pR)=pL:=by ext i;simp
  rw [momentum] at ward
  have charge : rawChargeCore a (sourceTestApprox q.F y)=weightCore (chargeAction (originalUnit a) (sourceTestApprox q.F y)) := by
    rw [rawChargeCore_source,LinearMap.sub_apply,LinearMap.comp_apply,sourceActualN1Primal_normalCharge_zero q pR state z t nonreal,sub_zero]
  have defect : rawChargeCore a (rightCompressionDefect pR q.F y+rightUncutDefect pR q.F y)=
      weightCore (chargeAction (originalUnit a) (rightCompressionDefect pR q.F y+rightUncutDefect pR q.F y)) := by
    rw [rawChargeCore_source,LinearMap.sub_apply,LinearMap.comp_apply,sourceActualN1Primal_rightDefect_normal_zero q pR state z t nonreal,sub_zero]
  exact replace_three (fun w r d : QuantumTest=>sourceApprox q.F (embed w)+
    leftCompressionDefect pL q.F r+leftUncutDefect pL q.F r-sourceApprox q.F (embed d)) ward charge defect

theorem sourceColorWardReturn_N1 (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    sourceColorWardReturn q pL pR (sourceActualN1Primal q pR state z t)=
      sourceN1ColorWardReturn q pL pR (sourceActualN1Primal q pR state z t) := by
  exact congrArg₂ (fun u v : H=>(1/2 : ℝ) • (u-v))
    (actualGaugeWard_return_N1 q pL pR state z t nonreal 6)
    (actualGaugeWard_return_N1 q pL pR state z t nonreal 7)

def sourceActualN1ColorWardRead (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) : ℂ :=
  -Complex.I*((sourcePoleDual q.epsilon q.precision pL left).comp
    (physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0))
      (sourceN1ColorWardReturn q pL pR (sourceActualN1Primal q pR right q.w t))

theorem sourceActualColorWardRead_N1 (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (nonreal : q.w.im≠0) :
    sourceActualColorWardRead q pL pR left right t=sourceActualN1ColorWardRead q pL pR left right t := by
  unfold sourceActualColorWardRead
  change -Complex.I*((sourcePoleDual q.epsilon q.precision pL left).comp
    (physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0))
      (sourceColorWardReturn q pL pR (sourceActualN1Primal q pR right q.w t))=_
  rw [sourceColorWardReturn_N1 q pL pR right q.w t nonreal]
  rfl

theorem sourceActualCosource114_N1WardBoundary (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceActualCurrentCosource q pL pR left right spatial lambda T 114=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceActualN1ColorWardRead q pL pR left right t)+
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceConstraintCovariant q pL pR left right spatial t)-
        (laplaceWeight lambda T*sourceConstraintCharge q pL pR left right T-
          sourceConstraintCharge q pL pR left right 0) := by
  rw [sourceActualCosource114_actualWardBoundary q pL pR left right spatial lambda T nonrealL nonrealR]
  simp_rw [sourceActualColorWardRead_N1 q pL pR left right _ nonrealR]

end LowEnergy.PreparationVacuumPhysicalN1WardCollapse
