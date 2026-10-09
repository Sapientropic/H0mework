import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstPoleGaugeReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCoframeChargePotential

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalResponseChargeGrading
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalNormalizedFullField
open PreparationPhysicalCoframeChargeSelection PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalNativePhaseChargeInventory PreparationPhysicalNativeOriginPhaseWard
open PreparationVacuumOriginalGreenFeedback PreparationVacuumNonlinearFieldCurve
open PreparationVacuumLowerClassical PreparationVacuumSourceFieldFamily
open PreparationVacuumPhysicalGaussMaterialContact PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalFeedback PreparationVacuumNativeSlowCoupling
open GaussNativeMatter GaussHistoryHilbert SourceQuantumFockGauge SourceQuantumResidualGaugeSlice
open CanonicalGradedCharge CanonicalGradedSpatialSource GaussQuantumMultiplier
open DiracCliffordRepresentation DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage10.CanonicalMatter Electromagnetic.CanonicalCoframe
open FullQuantum.CoframeResponse FullQuantum.StateGreen
open YangMills.FullPairing
open scoped Matrix BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _

private abbrev primalCharge : SourceMatrix :=
  Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)

/-- The actual global phase charge commutes with the complete spin action before any prepared-state restriction. -/
theorem sourcePoleSpin_charge (A : DiracMatrix) :
    Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)*spinCoordinates A=
      spinCoordinates A*Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether) := by
  have native:=GaussMatterCore.spin_native_commute A (colorGenerator 2)
  rw [←GaussCoframeSpin.spinLift_source] at native
  change spinCoordinates A*nativePrimal (colorGenerator 2)=
    nativePrimal (colorGenerator 2)*spinCoordinates A at native
  simp only [sourceCoframeCharge_primal,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,native]

/-- Independent conjugate branches retain their original minus-star order. -/
theorem sourcePoleSpin_branches_charge (A : DiracMatrix) :
    sourceActualGaussChargeMatrix*SourceRealScalarFock.branches (spinCoordinates A)=
      SourceRealScalarFock.branches (spinCoordinates A)*sourceActualGaussChargeMatrix := by
  have primal:=sourcePoleSpin_charge A
  have dual:=congrArg (fun M : SourceMatrix=>M.map (starRingEnd ℂ)) primal
  simp only [Matrix.map_mul] at dual
  change Matrix.fromBlocks primalCharge 0 0 (-(primalCharge.map (starRingEnd ℂ)))*
    Matrix.fromBlocks (spinCoordinates A) 0 0 (-((spinCoordinates A).map (starRingEnd ℂ)))=
    Matrix.fromBlocks (spinCoordinates A) 0 0 (-((spinCoordinates A).map (starRingEnd ℂ)))*
      Matrix.fromBlocks primalCharge 0 0 (-(primalCharge.map (starRingEnd ℂ)))
  simp only [Matrix.fromBlocks_multiply,zero_mul,mul_zero,add_zero,zero_add,neg_mul_neg]
  rw [primal,dual]

/-- Original full200 channel2 energy is neutral under the same full504 source charge, including every spin and internal state. -/
theorem sourceSecondPoleEnergy_charge (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    sourceActualGaussChargeMatrix*sourceLiteralEnergyWeight p (sourceState sourcePoint.val) v 2-
      sourceLiteralEnergyWeight p (sourceState sourcePoint.val) v 2*sourceActualGaussChargeMatrix=0 := by
  rw [sourceLiteralChannelTwoEnergy]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,sourcePoleSpin_branches_charge,sub_self]

/-- The generated neutral channel reaches the complete CAR operator, without a four-column or commutative-Green premise. -/
theorem sourceSecondPoleEnergy_fiber_charge (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    quantized sourceActualGaussChargeMatrix*
        quantized (sourceLiteralEnergyWeight p (sourceState sourcePoint.val) v 2)-
      quantized (sourceLiteralEnergyWeight p (sourceState sourcePoint.val) v 2)*
        quantized sourceActualGaussChargeMatrix=0 := by
  have generated:=congrArg quantizer (sourceSecondPoleEnergy_charge p v)
  rw [paidCoframeQuantizerComm%,map_zero] at generated
  exact generated

end LowEnergy.PreparationPhysicalResponseChargeGrading
