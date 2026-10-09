import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceN1GaussMaterialWard

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalN1MaterialWard
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
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

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

open PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation


open PreparationVacuumPhysicalModeContact GaussLiveMomentum CanonicalPhysicalWardCore




open scoped ContDiff



open PreparationVacuumPhysicalGaussColorTorque



open FullQuantum
open scoped Matrix.Norms.L2Operator

local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace




open PreparationVacuumPhysicalGaussMaterialContact PreparationVacuumActionDecomposition
open CanonicalPhysicalSpatial






theorem sourceColourChargeMatrix_generated :
    (1/2 : ℂ) • (chargeMatrix (originalUnit 6)-chargeMatrix (originalUnit 7))=chargeMatrix (colorGenerator 2) := by
  have native:=congrArg nativeFull sourceConstraintDirection_color
  simp only [map_smul,map_sub] at native
  have h : (1/2 : ℂ) • (nativeFull (originalUnit 6)-nativeFull (originalUnit 7))=nativeFull (colorGenerator 2) := by
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ)] at native
    norm_num at native
    exact native
  unfold chargeMatrix
  rw [←h]
  simp only [smul_sub]
  simp only [smul_comm (1/2 : ℂ) Complex.I]

theorem sourceColourChargeAction_generated :
    (1/2 : ℂ) • (chargeAction (originalUnit 6)-chargeAction (originalUnit 7))=chargeAction (colorGenerator 2) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change (1/2 : ℂ) • (quantizer (chargeMatrix (originalUnit 6)) (f x)-quantizer (chargeMatrix (originalUnit 7)) (f x))=
    quantizer (chargeMatrix (colorGenerator 2)) (f x)
  rw [←sourceColourChargeMatrix_generated,map_smul,map_sub]
  simp only [smul_apply,sub_apply]

private theorem raw_half (f : QuantumTest) (zero6 : normalChargeCore 6 f=0) (zero7 : normalChargeCore 7 f=0) :
    (1/2 : ℂ) • (rawChargeCore 6 f-rawChargeCore 7 f)=weightCore (chargeAction (colorGenerator 2) f) := by
  rw [rawChargeCore_source,rawChargeCore_source]
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,zero6,zero7,sub_zero]
  rw [←sourceColourChargeAction_generated]
  simp only [LinearMap.smul_apply,LinearMap.sub_apply,map_smul,map_sub]

private theorem combine_current {M : Type*} [AddCommGroup M] [Module ℂ M]
    (L : M→ₗ[ℂ] M) (c : ℂ) (X Y U V : M) :
    c • ((L X-U)-(L Y-V))=L (c • (X-Y))-c • (U-V) := by
  simp only [map_smul,map_sub,smul_sub]
  abel

def sourceColourWeightedWard (pL pR : PhysicalMomentum) (f : QuantumTest) : QuantumTest :=
  (1/2 : ℂ) • (weightedWardCore pR (pL-pR) 6 f-weightedWardCore pR (pL-pR) 7 f)

theorem sourceActualN1ColourWeightedWard_generated (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (pL pR : PhysicalMomentum) :
    sourceColourWeightedWard pL pR (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=
      weightCore (fullSourceAction pL (chargeAction (colorGenerator 2)
        (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))-
        chargeAction (colorGenerator 2) (fullSourceAction pR (sourceTestApprox q.F (sourceActualN1Primal q p state z t))))+
      weightActionTorque pL (chargeAction (colorGenerator 2) (sourceTestApprox q.F (sourceActualN1Primal q p state z t))) := by
  let f:=sourceTestApprox q.F (sourceActualN1Primal q p state z t)
  have momentum : pR+(pL-pR)=pL := by ext i;change pR i+(pL i-pR i)=pL i;ring
  unfold sourceColourWeightedWard
  rw [←rawCharge_original_action_ward pR (pL-pR) 6,←rawCharge_original_action_ward pR (pL-pR) 7,momentum]
  change (1/2 : ℂ) • ((fullSourceAction pL (rawChargeCore 6 f)-rawChargeCore 6 (fullSourceAction pR f))-
    (fullSourceAction pL (rawChargeCore 7 f)-rawChargeCore 7 (fullSourceAction pR f)))=_
  rw [combine_current]
  have raw:=raw_half f (sourceActualN1Primal_normalCharge_zero q p state z t nonreal 6)
    (sourceActualN1Primal_normalCharge_zero q p state z t nonreal 7)
  have after:=raw_half (fullSourceAction pR f)
    (sourceActualN1Primal_fullSource_normal_zero q p state z t nonreal pR 6)
    (sourceActualN1Primal_fullSource_normal_zero q p state z t nonreal pR 7)
  rw [raw,after]
  unfold weightActionTorque
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,map_sub]
  abel


private theorem sourceRelativeN1Ward (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (pL pR : PhysicalMomentum) :
    fullSourceAction pL (chargeAction (colorGenerator 2) (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))-
      chargeAction (colorGenerator 2) (fullSourceAction pR (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))-
      CanonicalPhysicalWardCore.currentAction (pL-pR) (colorGenerator 2)
        (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=
      sourceColorWardOperator (fullSourceAction pR) (sourceTestApprox q.F (sourceActualN1Primal q p state z t)) := by
  let f:=sourceTestApprox q.F (sourceActualN1Primal q p state z t)
  have momentum : pR+(pL-pR)=pL := by ext i;change pR i+(pL i-pR i)=pL i;ring
  have rel:=original_full_ward pR (pL-pR) (colorGenerator 2) f
  have same:=original_full_ward pR 0 (colorGenerator 2) f
  change fullSourceAction (pR+(pL-pR)) (chargeAction (colorGenerator 2) f)-
    chargeAction (colorGenerator 2) (fullSourceAction pR f)=wardCore (pL-pR) (colorGenerator 2) f at rel
  change fullSourceAction (pR+0) (chargeAction (colorGenerator 2) f)-
    chargeAction (colorGenerator 2) (fullSourceAction pR f)=wardCore 0 (colorGenerator 2) f at same
  rw [momentum] at rel
  have pair (k : PhysicalMomentum) : pairCurrent k (colorGenerator 2) f=0 :=
    sourceActualN1Primal_pairCurrent_zero q p state z t nonreal k (colorGenerator 2)
  simp only [wardCore,LinearMap.add_apply,pair,add_zero] at rel
  simp only [add_zero,wardCore,LinearMap.add_apply,pair,
    CanonicalPhysicalWardCore.currentAction,Pi.zero_apply,Complex.ofReal_zero,zero_smul,Finset.sum_const_zero,add_zero] at same
  change fullSourceAction pL (chargeAction (colorGenerator 2) f)-chargeAction (colorGenerator 2) (fullSourceAction pR f)-
    CanonicalPhysicalWardCore.currentAction (pL-pR) (colorGenerator 2) f=
    fullSourceAction pR (chargeAction (colorGenerator 2) f)-chargeAction (colorGenerator 2) (fullSourceAction pR f)
  rw [rel,same]
  abel_nf

theorem sourceActualN1Native_weightedColourWard (q : PhysicalResponsePoint) (pR : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (pL : PhysicalMomentum) :
    sourceNativeContactCore pR (sourceTestApprox q.F (sourceActualN1Primal q pR state z t))=
      (-Complex.I) • (sourceColourWeightedWard pL pR (sourceTestApprox q.F (sourceActualN1Primal q pR state z t))-
        weightActionTorque pL (chargeAction (colorGenerator 2) (sourceTestApprox q.F (sourceActualN1Primal q pR state z t)))-
        weightCore (CanonicalPhysicalWardCore.currentAction (pL-pR) (colorGenerator 2) (sourceTestApprox q.F (sourceActualN1Primal q pR state z t)))-
        weightCore (sourceColorWardOperator GaussNativeForm.nativeAction (sourceTestApprox q.F (sourceActualN1Primal q pR state z t)))+
        weightCore (sourceColorWardOperator retainedCore (sourceTestApprox q.F (sourceActualN1Primal q pR state z t)))) := by
  rw [sourceActualN1MaterialContact_gauss q pR state z t nonreal,
    sourceActualN1ColourWeightedWard_generated q pR state z t nonreal pL pR]
  have rel:=congrArg weightCore (sourceRelativeN1Ward q pR state z t nonreal pL pR)
  simp only [map_sub] at rel
  simp only [map_add,map_sub]
  rw [←rel]
  congr 1
  abel_nf

def sourceColourContactWardCore (pL pR : PhysicalMomentum) (f : QuantumTest) : QuantumTest :=
  Complex.I • sourceNativeContactCore pR f+
    weightActionTorque pL (chargeAction (colorGenerator 2) f)+
    weightCore (CanonicalPhysicalWardCore.currentAction (pL-pR) (colorGenerator 2) f)+
    weightCore (sourceColorWardOperator GaussNativeForm.nativeAction f)-
    weightCore (sourceColorWardOperator retainedCore f)

private theorem solve_contact {M : Type*} [AddCommGroup M] [Module ℂ M]
    (u v a b c d : M) (h : u=(-Complex.I) • (v-a-b-c+d)) :
    v=Complex.I • u+a+b+c-d := by
  rw [h,smul_smul]
  have scalar : Complex.I*(-Complex.I)=1 := by simp
  rw [scalar,one_smul]
  abel_nf

theorem sourceActualN1ColourContactWard_core (q : PhysicalResponsePoint) (pR : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (pL : PhysicalMomentum) :
    sourceColourWeightedWard pL pR (sourceTestApprox q.F (sourceActualN1Primal q pR state z t))=
      sourceColourContactWardCore pL pR (sourceTestApprox q.F (sourceActualN1Primal q pR state z t)) :=
  solve_contact _ _ _ _ _ _ (sourceActualN1Native_weightedColourWard q pR state z t nonreal pL)

private theorem half_return {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (L C U : A→ₗ[ℂ] B) (c : ℂ) (v w r s d e : A) :
    c • ((L v+C r+U r-L d)-(L w+C s+U s-L e))=
      L (c • (v-w))+C (c • (r-s))+U (c • (r-s))-L (c • (d-e)) := by
  simp only [map_smul,map_sub,smul_sub,smul_add]
  abel_nf

private theorem real_half (x : H) : (1/2 : ℝ) • x=(1/2 : ℂ) • x := by
  simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  norm_num

def sourceColourContactWardReturn (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (y : H) : H :=
  sourceApprox q.F (embed (sourceColourContactWardCore pL pR (sourceTestApprox q.F y)))+
    leftCompressionDefect pL q.F (weightCore (chargeAction (colorGenerator 2) (sourceTestApprox q.F y)))+
    leftUncutDefect pL q.F (weightCore (chargeAction (colorGenerator 2) (sourceTestApprox q.F y)))-
    sourceApprox q.F (embed (weightCore (chargeAction (colorGenerator 2)
      (rightCompressionDefect pR q.F y+rightUncutDefect pR q.F y))))

theorem sourceActualN1ColourContactWard_return (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    sourceN1ColorWardReturn q pL pR (sourceActualN1Primal q pR state z t)=
      sourceColourContactWardReturn q pL pR (sourceActualN1Primal q pR state z t) := by
  let y:=sourceActualN1Primal q pR state z t
  let f:=sourceTestApprox q.F y
  let d:=rightCompressionDefect pR q.F y+rightUncutDefect pR q.F y
  let L:QuantumTest→ₗ[ℂ] H:=(sourceApprox q.F).toLinearMap.comp embed
  let C:QuantumTest→ₗ[ℂ] H:=(compression pL q.F).toLinearMap.comp L-L.comp (physicalAction pL)
  let U:QuantumTest→ₗ[ℂ] H:=(sourceUncutAction pL q.F).toLinearMap.comp L-L.comp GaussYukawaOperator.originalAction
  have momentum : pR+(pL-pR)=pL := by ext i;simp
  have ward6:=sourceActualN1Primal_weightedWard q pR state z t nonreal pR (pL-pR) 6
  have ward7:=sourceActualN1Primal_weightedWard q pR state z t nonreal pR (pL-pR) 7
  rw [momentum] at ward6 ward7
  unfold sourceN1ColorWardReturn
  rw [real_half]
  unfold sourceN1GaugeWardReturn
  change (1/2 : ℂ) • ((L (weightCore (sourceN1WardCore (pL-pR) (originalUnit 6) f)+
    weightActionTorque pL (chargeAction (originalUnit 6) f))+C (weightCore (chargeAction (originalUnit 6) f))+
    U (weightCore (chargeAction (originalUnit 6) f))-L (weightCore (chargeAction (originalUnit 6) d)))-
    (L (weightCore (sourceN1WardCore (pL-pR) (originalUnit 7) f)+
    weightActionTorque pL (chargeAction (originalUnit 7) f))+C (weightCore (chargeAction (originalUnit 7) f))+
    U (weightCore (chargeAction (originalUnit 7) f))-L (weightCore (chargeAction (originalUnit 7) d))))=_
  rw [←ward6,←ward7,half_return]
  have weighted (g : QuantumTest) :
      (1/2 : ℂ) • (weightCore (chargeAction (originalUnit 6) g)-weightCore (chargeAction (originalUnit 7) g))=
        weightCore (chargeAction (colorGenerator 2) g) := by
    rw [←map_sub,←map_smul]
    exact congrArg weightCore (congrArg (fun A : QuantumEnd=>A g) sourceColourChargeAction_generated)
  rw [weighted f,weighted d]
  change L (sourceColourWeightedWard pL pR f)+C (weightCore (chargeAction (colorGenerator 2) f))+
    U (weightCore (chargeAction (colorGenerator 2) f))-L (weightCore (chargeAction (colorGenerator 2) d))=_
  rw [sourceActualN1ColourContactWard_core q pR state z t nonreal pL]
  rfl

def sourceActualColourContactWardRead (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) : ℂ :=
  -Complex.I*((sourcePoleDual q.epsilon q.precision pL left).comp
    (physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0))
      (sourceColourContactWardReturn q pL pR (sourceActualN1Primal q pR right q.w t))

theorem sourceActualColourContactWard_read (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (nonreal : q.w.im≠0) :
    sourceActualN1ColorWardRead q pL pR left right t=sourceActualColourContactWardRead q pL pR left right t := by
  unfold sourceActualN1ColorWardRead sourceActualColourContactWardRead
  rw [sourceActualN1ColourContactWard_return q pL pR right q.w t nonreal]

theorem sourceActualCosource114_ColourContactWard (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceActualCurrentCosource q pL pR left right spatial lambda T 114=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceActualColourContactWardRead q pL pR left right t)+
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceConstraintCovariant q pL pR left right spatial t)-
        (laplaceWeight lambda T*sourceConstraintCharge q pL pR left right T-
          sourceConstraintCharge q pL pR left right 0) := by
  rw [sourceActualCosource114_N1WardBoundary q pL pR left right spatial lambda T nonrealL nonrealR]
  simp_rw [sourceActualColourContactWard_read q pL pR left right _ nonrealR]

end LowEnergy.PreparationVacuumPhysicalN1MaterialWard
