import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationActualQuantumMaterialWard

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


private theorem three_oneParticle (A B C : FullMatrix) (w : Mode→ℂ) :
    quantized A (quantized B (quantized C (oneParticleFiber w)))=quantized (A*(B*C)) (oneParticleFiber w) := by
  rw [quantized_product_oneParticle B C w,quantized_product_oneParticle A (B*C) w]

private theorem negative_flip {M : Type*} [AddCommGroup M] [Module ℂ M] (c : ℂ) (u v : M) :
    c • (u-v)=(-c) • (v-u) := by
  simp only [smul_sub,neg_smul]
  abel

theorem sourceN1MaterialContact_oneParticle (p : PhysicalMomentum) (z : physicalChart) (w : Mode→ℂ) :
    quantizer (nativeRaw (Fin.castAdd 6 (2:Fin 3)) 1 0 p (sourceState z.val)) (oneParticleFiber w)=
      (-Complex.I) • weightFiber z.val
        (actualFiber p z.val (sourceColorChargeFiber (oneParticleFiber w))-
          sourceColorChargeFiber (actualFiber p z.val (oneParticleFiber w))) := by
  rw [sourceColourRaw_material,map_smul]
  simp only [smul_apply]
  change (4*Complex.I) • quantized (chargeMatrix (colorGenerator 2)*(sourceActionWeight (sourceState z.val)*sourceSymbol p (sourceState z.val))-
      (sourceActionWeight (sourceState z.val)*sourceSymbol p (sourceState z.val))*chargeMatrix (colorGenerator 2)) (oneParticleFiber w)=
    (-Complex.I) • quantized ((4:ℂ) • sourceActionWeight (sourceState z.val))
      (quantized (sourceSymbol p (sourceState z.val)) (quantized (chargeMatrix (colorGenerator 2)) (oneParticleFiber w))-
        quantized (chargeMatrix (colorGenerator 2)) (quantized (sourceSymbol p (sourceState z.val)) (oneParticleFiber w)))
  change (4*Complex.I) • (quantizer (_-_) (oneParticleFiber w))=_
  rw [map_sub]
  simp only [sub_apply]
  change (4*Complex.I) • (quantized _ (oneParticleFiber w)-quantized _ (oneParticleFiber w))=_
  simp only [mul_assoc]
  rw [←three_oneParticle,←three_oneParticle]
  change _=(-Complex.I) • ((quantizer ((4:ℂ) • sourceActionWeight (sourceState z.val))) (_-_))
  rw [map_smul,map_sub]
  simp only [smul_apply,smul_sub,smul_smul]
  have coefficient : (-Complex.I)*(4:ℂ)=-(4*Complex.I) := by ring
  rw [coefficient]
  have commute : Commute (quantized (chargeMatrix (colorGenerator 2))) (quantized (sourceActionWeight (sourceState z.val))) :=
    CanonicalPhysicalForce.quantized_commute _ _ (by
      change (Complex.I • nativeFull (colorGenerator 2))*sourceActionWeight (sourceState z.val)=
        sourceActionWeight (sourceState z.val)*(Complex.I • nativeFull (colorGenerator 2))
      rw [smul_mul_assoc,mul_smul_comm,(sourceColour_weight (sourceState z.val)).eq])
  have h := congrArg (fun T : FockFiber→L[ℂ] FockFiber=>T (quantized (sourceSymbol p (sourceState z.val)) (oneParticleFiber w))) commute.eq
  change quantized (chargeMatrix (colorGenerator 2)) (quantized (sourceActionWeight (sourceState z.val)) _)=
    quantized (sourceActionWeight (sourceState z.val)) (quantized (chargeMatrix (colorGenerator 2)) _) at h
  rw [h]
  simpa only [quantizer,LinearMap.coe_mk,AddHom.coe_mk,smul_sub,neg_smul] using
    negative_flip (4*Complex.I)
      (quantized (sourceActionWeight (sourceState z.val)) (quantized (chargeMatrix (colorGenerator 2)) (quantized (sourceSymbol p (sourceState z.val)) (oneParticleFiber w))))
      (quantized (sourceActionWeight (sourceState z.val)) (quantized (sourceSymbol p (sourceState z.val)) (quantized (chargeMatrix (colorGenerator 2)) (oneParticleFiber w))))


theorem sourceN1MaterialContact_label (p : PhysicalMomentum) (z : physicalChart)
    (g : NativeHistoryGrade.Label) (one : g.1.val=1) (f : QuantumTest) :
    quantizer (nativeRaw (Fin.castAdd 6 (2:Fin 3)) 1 0 p (sourceState z.val)) ((GaussCoreLabel.project g f) z.val)=
      (-Complex.I) • weightFiber z.val
        (actualFiber p z.val (sourceColorChargeFiber ((GaussCoreLabel.project g f) z.val))-
          sourceColorChargeFiber (actualFiber p z.val ((GaussCoreLabel.project g f) z.val))) := by
  change quantizer _ (GaussCoreLabel.fiberPiece g (f z.val))=
    (-Complex.I) • weightFiber z.val
      (actualFiber p z.val (sourceColorChargeFiber (GaussCoreLabel.fiberPiece g (f z.val)))-
        sourceColorChargeFiber (actualFiber p z.val (GaussCoreLabel.fiberPiece g (f z.val))))
  rw [sourceNumberOne_oneParticle g one (f z.val)]
  exact sourceN1MaterialContact_oneParticle p z _

private theorem linear_sum (K L : FockFiber→L[ℂ] FockFiber) (x x₀ x₁ : FockFiber)
    (sum : x₀+x₁=x) (zero : K x₀=L x₀) (one : K x₁=L x₁) : K x=L x := by
  rw [←sum,map_add,map_add,zero,one]

theorem sourceActualN1MaterialContact_point (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (x : physicalChart) :
    quantizer (nativeRaw (Fin.castAdd 6 (2:Fin 3)) 1 0 p (sourceState x.val))
      (sourceTestApprox q.F (sourceActualN1Primal q p state z t) x.val)=
      (-Complex.I) • weightFiber x.val
        (actualFiber p x.val (sourceColorChargeFiber (sourceTestApprox q.F (sourceActualN1Primal q p state z t) x.val))-
          sourceColorChargeFiber (actualFiber p x.val (sourceTestApprox q.F (sourceActualN1Primal q p state z t) x.val))) := by
  let f:=sourceTestApprox q.F (sourceActualN1Primal q p state z t)
  have sum:=congrArg (fun v : QuantumTest=>v x.val) (sourceActualN1Primal_core q p state z t nonreal)
  exact linear_sum (quantizer (nativeRaw (Fin.castAdd 6 (2:Fin 3)) 1 0 p (sourceState x.val)))
    ((-Complex.I) • weightFiber x.val*(actualFiber p x.val*sourceColorChargeFiber-sourceColorChargeFiber*actualFiber p x.val))
    (f x.val) ((GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel f) x.val)
    ((GaussCoreLabel.project sourceExcitedLabel f) x.val) sum
    (sourceN1MaterialContact_label p x CanonicalGradedCurrent.sourceLabel rfl f)
    (sourceN1MaterialContact_label p x sourceExcitedLabel rfl f)

end LowEnergy.PreparationVacuumPhysicalN1MaterialWard
