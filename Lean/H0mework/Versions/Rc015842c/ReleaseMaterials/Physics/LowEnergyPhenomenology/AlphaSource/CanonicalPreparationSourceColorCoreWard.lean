import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceColorBalance
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationWeightedChargePreparedActionReturn

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalColorWard
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

theorem sourceNumberOne_oneParticle (g : Label) (one : g.1.val=1) (v : FockFiber) :
    GaussCoreLabel.fiberPiece g v=
      oneParticleFiber (fun i=>GaussCoreLabel.fiberPiece g v {i}) := by
  apply PiLp.ext
  intro word
  change GaussCoreLabel.fiberPiece g v word=oneParticle (fun i=>GaussCoreLabel.fiberPiece g v {i}) word
  by_cases singleton : ∃ i : Mode,word={i}
  · obtain ⟨i,rfl⟩:=singleton
    rw [oneParticle_singleton]
  · have hn : ∀ i : Mode,word≠{i}:=by simpa only [not_exists] using singleton
    rw [oneParticle_eq_zero_of_not_singleton _ word hn,GaussCoreLabel.fiberPiece_apply]
    apply if_neg
    intro equal
    have card:=congrArg (fun l : Label=>l.1.val) equal
    rw [one] at card
    exact singleton (Finset.card_eq_one.mp card)

theorem sourceNumberOne_quantized_product (g : Label) (one : g.1.val=1) (A B : FullMatrix) :
    quantized A*quantized B*GaussCoreLabel.fiberPiece g=
      quantized (A*B)*GaussCoreLabel.fiberPiece g := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [mul_apply_eq_comp]
  rw [sourceNumberOne_oneParticle g one v]
  exact quantized_product_oneParticle A B _

theorem sourceNumberOne_pairFiber_zero (g : Label) (one : g.1.val=1) (A B : FullMatrix) :
    pairFiber A B*GaussCoreLabel.fiberPiece g=0 := by
  rw [pairFiber_sub,sub_mul,sourceNumberOne_quantized_product g one A B,sub_self]

theorem sourceNumberOne_normalChargeCore_zero (g : Label) (one : g.1.val=1) (a : Fin 12)
    (f : QuantumTest) : normalChargeCore a (GaussCoreLabel.project g f)=0 := by
  apply DFunLike.ext
  intro z
  have h:=sourceNumberOne_pairFiber_zero g one (sourceWeightSymbol z) (chargeMatrix (originalUnit a))
  have value:=congrArg (fun T : FockFiber→L[ℂ] FockFiber=>T (f z)) h
  exact value

theorem sourceNumberOne_rawChargeCore (g : Label) (one : g.1.val=1) (a : Fin 12)
    (f : QuantumTest) : rawChargeCore a (GaussCoreLabel.project g f)=
      weightCore (chargeAction (originalUnit a) (GaussCoreLabel.project g f)) := by
  rw [rawChargeCore_source,LinearMap.sub_apply,LinearMap.comp_apply,sourceNumberOne_normalChargeCore_zero g one,sub_zero]

theorem sourceGradeZero_normalCharge_zero (a : Fin 12) (f : QuantumTest) :
    normalChargeCore a (GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel f)=0 :=
  sourceNumberOne_normalChargeCore_zero _ rfl a f

theorem sourceGradeOne_normalCharge_zero (a : Fin 12) (f : QuantumTest) :
    normalChargeCore a (GaussCoreLabel.project sourceExcitedLabel f)=0 :=
  sourceNumberOne_normalChargeCore_zero _ rfl a f

end LowEnergy.PreparationVacuumPhysicalColorWard
