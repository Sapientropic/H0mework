import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceVoltageFourModeEnergy

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFilteredChargeVoltage
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage9DEF.Compatibility Stage9C.Material.SpinPair Stage10
open DiracExteriorMatterAction YangMills.FullPairing FullQuantum FullSpace FullQuantum.Triangular
open Stage10.CanonicalMatter Electromagnetic FullQuantum.SpatialResponse
open StageNineHolonomicField SU7MotherLieAlgebra FullQuantum.PerturbedGreen FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalVoltageEnergyIdentity PreparationPhysicalVoltageNoether PreparationPhysicalChargedEnergyVariation
open PreparationVacuumVoltageGaussGreen PreparationVacuumPhysicalModeChargeRead GaussComposite
open PreparationVacuumNativeFieldInjection GaussHistoryHilbert
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] CanonicalPacket.densityReader sourceEnergyMatrixRead sourceVoltageHamiltonianMatrix

/-- The original phaseInverse density leg and the original voltage energy insertion have opposite sign. -/
theorem sourceCanonicalCharge_voltage :
    CanonicalPacket.densityReader (currentAction 0 HyperchargeResponse.chargeDirection)=
      -sourceEnergyMatrixRead (sourceVoltageHamiltonianMatrix 1 0 sourceVoltageActualState) := by
  rw [sourceVoltageHamiltonian_split _ (PreparationVacuumNonlinearFieldCurve.sourceState_valid sourcePoint).2]
  simp only [one_smul,zero_smul,add_zero]
  unfold CanonicalPacket.densityReader sourceEnergyMatrixRead
  change operator canonicalCharge=-operator (Quantum.operatorMatrix.symm
    ((-Complex.I) • Quantum.operatorMatrix (diracExteriorMotherLieAction
      (p286LieBlockEmbed (p286CoordinateEquiv.symm nativeY)))))
  rw [map_smul,Quantum.operatorMatrix.symm_apply_apply,operator_smul,nativeY,p286CoordinateEquiv.symm_apply_apply]
  have charge : canonicalCharge=Complex.I • diracExteriorMotherLieAction
      (p286LieBlockEmbed HyperchargeResponse.chargeDirection) := by
    apply LinearMap.ext
    intro matter
    exact canonical_charge_source matter
  rw [charge,operator_smul]
  module

/-- Both actual filtered legs stay in the paid original reducing image almost everywhere. -/
theorem sourceFilteredPacket_retained_ae (side edge : Fin 2) :
    (fun x=>sourceVoltageFiberProjection (sourceChargedFilteredPacket side edge x))=ᵐ[volume]
      sourceChargedFilteredPacket side edge := by
  have generated:=sourceVoltageFiberProjection.coeFn_compLpL (sourceChargedFilteredPacket side edge)
  change sourceVoltageSpatialProjection (sourceChargedFilteredPacket side edge)=ᵐ[volume]
    (fun x=>sourceVoltageFiberProjection (sourceChargedFilteredPacket side edge x)) at generated
  rw [sourceChargedFilteredPacket_retained] at generated
  exact generated.symm

/-- The physical current uses the source canonical density reader, including its independent momentum dual. -/
def sourceFilteredCurrent (sideL edgeL sideR edgeR : Fin 2) (x : Position) : ℂ :=
  (4*(spinScale:ℂ))*inner ℂ (sourceChargedFilteredPacket sideL edgeL x)
    (CanonicalPacket.densityReader (currentAction 0 HyperchargeResponse.chargeDirection)
      (sourceChargedFilteredPacket sideR edgeR x))

theorem sourceFilteredCurrent_pair (sideL edgeL sideR edgeR : Fin 2) :
    sourceFilteredCurrent sideL edgeL sideR edgeR=ᵐ[volume]
      fun x=>-(ActionNormalization.phaseMomentum:ℂ)*
        inner ℂ (sourceChargedFilteredPacket sideL edgeL x) (sourceChargedFilteredPacket sideR edgeR x) := by
  filter_upwards [sourceFilteredPacket_retained_ae sideL edgeL,sourceFilteredPacket_retained_ae sideR edgeR]
    with x left right
  rw [sourceFilteredCurrent,sourceCanonicalCharge_voltage,neg_apply,inner_neg_right]
  rw [sourceVoltageHamiltonian_pair sourceVoltageActualState
    (PreparationVacuumNonlinearFieldCurve.sourceState_valid sourcePoint).2 1 0 _ _ left right]
  simp only [Complex.ofReal_one,one_mul,ActionNormalization.phaseMomentum_source,Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

theorem sourceFilteredCurrent_integrable (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (sourceFilteredCurrent sideL edgeL sideR edgeR) :=
  ((L2.integrable_inner (𝕜:=ℂ) (sourceChargedFilteredPacket sideL edgeL)
    (sourceChargedFilteredPacket sideR edgeR)).const_mul (-(ActionNormalization.phaseMomentum:ℂ))).congr
      (sourceFilteredCurrent_pair sideL edgeL sideR edgeR).symm

theorem sourceFilteredCurrent_integral (sideL edgeL sideR edgeR : Fin 2) :
    (∫x,sourceFilteredCurrent sideL edgeL sideR edgeR x)=
      -(ActionNormalization.phaseMomentum:ℂ)*inner ℂ
        (sourceChargedFilteredPacket sideL edgeL) (sourceChargedFilteredPacket sideR edgeR) := by
  rw [integral_congr_ae (sourceFilteredCurrent_pair sideL edgeL sideR edgeR),integral_const_mul,←L2.inner_def]

theorem sourceFilteredCurrent_total (side edge : Fin 2) :
    (∫x,sourceFilteredCurrent side edge side edge x)=-(ActionNormalization.phaseMomentum:ℂ) := by
  rw [sourceFilteredCurrent_integral,inner_self_eq_norm_sq_to_K,sourceChargedFilteredPacket_unit]
  norm_num

/-- The same physical current is an insertion in the original quantum state and both actual preparation maps. -/
def sourceFilteredChargeOperator : SpatialOperators :=
  (4*(spinScale:ℂ)) •
    (CanonicalPacket.densityReader (currentAction 0 HyperchargeResponse.chargeDirection)).compLpL 2 volume

theorem sourceFilteredCurrent_quantum (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedQuantumRead sideL edgeL sideR edgeR sourceFilteredChargeOperator=
      ∫x,sourceFilteredCurrent sideL edgeL sideR edgeR x := by
  rw [sourceChargedQuantumRead_generated,sourceFilteredChargeOperator,smul_apply,inner_smul_right,L2.inner_def,
    ←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(CanonicalPacket.densityReader (currentAction 0 HyperchargeResponse.chargeDirection)).coeFn_compLpL
    (sourceChargedFilteredPacket sideR edgeR)] with x actual
  rw [actual]
  rfl

end LowEnergy.PreparationPhysicalFilteredChargeVoltage
