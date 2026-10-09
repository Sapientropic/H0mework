import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedGreenRetention

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalVoltageEnergyIdentity
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage9DEF.Compatibility Stage9C.Material.SpinPair Stage10
open DiracExteriorMatterAction YangMills.FullPairing FullQuantum FullSpace
open FullQuantum.FullCurrentSymbol FullQuantum.Triangular ActiveSector
open FullQuantum.CoframeResponse FullQuantum.StateGreen
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorBreakingYukawa StageNineDynamicBreakingVacuum StageNineHolonomicField StageNineDiracDualYukawaSpinJurisdiction
open StageNineCurrentCoframeMatterTemporalPrincipal Stage10.TemporalGauge
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalVoltageNoether PreparationPhysicalChargedEnergyVariation PreparationPhysicalNormalizedFullField
open PreparationVacuumVoltageGaussGreen PreparationVacuumStaticVoltageSource
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumActualFieldQuantization GaussHistoryHilbert SourceQuantumScalarChart
open PreparationVacuumPhysicalModeChargeRead PreparationVacuumNativeFieldInjection GaussComposite
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _

/-- This is the original positive Hilbert pairing on the retained image; it does not replace the independent source dual. -/
theorem sourceVoltageProjection_pair (u v : Hilbert) :
    inner ℂ (sourceVoltageFiberProjection u) v=inner ℂ u (sourceVoltageFiberProjection v) := by
  obtain ⟨a,rfl⟩:=naturalCoordinates.surjective u
  obtain ⟨b,rfl⟩:=naturalCoordinates.surjective v
  simp only [sourceVoltageFiberProjection,operator_coordinates,natural_inner,←Quantum.coordinatePair_full]
  exact projection_pair a b

private theorem triplet_charge (color : Fin 3) :
    exteriorSpinorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection) (colorTripletMatter color)=
      Complex.I • colorTripletMatter color := by
  have weight : exteriorHyperchargeWeight (colorTripletIndex color)=1:=by fin_cases color <;> decide
  simp [colorTripletMatter,exteriorSpinorMotherLieAction,HyperchargeResponse.exterior_charge_basis,weight]

private theorem projection_charge (matter : DiracExteriorMatterCarrier) :
    diracExteriorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection) (ActiveSector.projection matter)=
      Complex.I • ActiveSector.projection matter := by
  funext spin
  change exteriorSpinorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
    (∑color : Fin 3,(su7ExteriorBasis 2).coord (colorTripletIndex color) (matter spin).2.1 • colorTripletMatter color)=
      Complex.I • (∑color : Fin 3,(su7ExteriorBasis 2).coord (colorTripletIndex color) (matter spin).2.1 • colorTripletMatter color)
  simp only [map_sum,map_smul,triplet_charge,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro color _
  exact smul_comm _ _ _

private theorem native_voltage_read :
    sourceEnergyMatrixRead ((-Complex.I) • GaussNativeMatter.nativePrimal nativeY)=
      (-Complex.I) • operator (diracExteriorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection)) := by
  change operator (Quantum.operatorMatrix.symm ((-Complex.I) • Quantum.operatorMatrix
    (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm nativeY)))))=_
  rw [map_smul,Quantum.operatorMatrix.symm_apply_apply,operator_smul,nativeY,p286CoordinateEquiv.symm_apply_apply]

private theorem scalar_voltage_read (s : ActionState) (regular : coframeTemporalPrincipalScalar s.1≠0) :
    sourceEnergyMatrixRead (sourceVoltageScalarHamiltonian s)=(-Complex.I) • operator
      (currentCoframeMatterTemporalPrincipalInverse s.1*
        diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (scalarCharge HyperchargeResponse.chargeDirection))) := by
  change operator (Quantum.operatorMatrix.symm ((-Complex.I) •
    (Ring.inverse (principalMatrix s.1)*sourceVoltageYukawaMatrix)))=_
  rw [principal_inverse_original s.1 regular]
  change operator (Quantum.operatorMatrix.symm ((-Complex.I) •
    (Quantum.operatorMatrix _*Quantum.operatorMatrix _)))=_
  rw [←map_mul,map_smul,Quantum.operatorMatrix.symm_apply_apply,operator_smul]

private theorem scalar_projection_zero (s : ActionState) (regular : coframeTemporalPrincipalScalar s.1≠0) :
    sourceVoltageFiberProjection*sourceEnergyMatrixRead (sourceVoltageScalarHamiltonian s)=0 := by
  rw [scalar_voltage_read s regular,mul_smul_comm]
  change (-Complex.I) • (operator ActiveSector.projection*operator (_*_))=0
  rw [←operator_mul]
  have reducing : Commute ActiveSector.projection (currentCoframeMatterTemporalPrincipalInverse s.1):=
    ((spin_reducing _).smul_right Complex.I).smul_right _
  have zero : ActiveSector.projection*diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm (scalarCharge HyperchargeResponse.chargeDirection))=0:=projection_yukawa_zero _
  rw [←mul_assoc,reducing.eq,mul_assoc,zero,mul_zero,operator_zero]
  exact _root_.smul_zero (M:=ℂ) (A:=FiberOperators) (-Complex.I)

/-- Scalar output is killed by the actually retained left source leg, without a full-space Yukawa-zero claim. -/
theorem sourceVoltageHamiltonian_pair (s : ActionState) (regular : coframeTemporalPrincipalScalar s.1≠0)
    (value slope : ℝ) (u v : Hilbert)
    (left : sourceVoltageFiberProjection u=u) (right : sourceVoltageFiberProjection v=v) :
    inner ℂ u (sourceEnergyMatrixRead (sourceVoltageHamiltonianMatrix value slope s) v)=
      (value:ℂ)*inner ℂ u v := by
  have charge : sourceEnergyMatrixRead ((-Complex.I) • GaussNativeMatter.nativePrimal nativeY) v=v := by
    rw [native_voltage_read]
    conv_lhs => rw [←right]
    obtain ⟨matter,rfl⟩:=naturalCoordinates.surjective v
    simp only [sourceVoltageFiberProjection,operator_coordinates,smul_apply]
    rw [projection_charge,map_smul,smul_smul]
    simp only [neg_mul,Complex.I_mul_I,neg_neg,one_smul]
    simpa only [sourceVoltageFiberProjection,operator_coordinates] using right
  have scalar : inner ℂ u (sourceEnergyMatrixRead (sourceVoltageScalarHamiltonian s) v)=0 := by
    rw [←left,sourceVoltageProjection_pair]
    have zero:=DFunLike.congr_fun (scalar_projection_zero s regular) v
    change sourceVoltageFiberProjection (sourceEnergyMatrixRead (sourceVoltageScalarHamiltonian s) v)=0 at zero
    rw [zero,inner_zero_right]
  rw [sourceVoltageHamiltonian_split s regular,map_add]
  rw [sourceEnergyMatrixRead.map_smul_of_tower value,sourceEnergyMatrixRead.map_smul_of_tower slope]
  simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),add_apply,smul_apply,inner_add_right,inner_smul_right,
    charge,scalar,mul_zero,add_zero]
  rfl

/-- The full normalized jet specializes to the same original voltage Hamiltonian coefficients. -/
theorem sourceVoltageEnergyJet_coefficients (value slope : ℝ) (k : Fin 4) :
    sourceHamiltonianJetMatrix sourceVoltageActualState (sourceVoltageStateDirection value slope) k=
      if k=0 then sourceVoltageHamiltonianMatrix value slope sourceVoltageActualState else 0 := by
  have generated:=sourceHamiltonianJetMatrix_derivative sourceVoltageActualState (sourceVoltageStateDirection value slope)
    (PreparationVacuumNonlinearFieldCurve.sourceState_valid sourcePoint) k
  have affine:=((hasDerivAt_id (0:ℝ)).smul_const
    (if k=0 then sourceVoltageHamiltonianMatrix value slope sourceVoltageActualState else 0)).const_add
      (stateHamiltonian sourceVoltageActualState k)
  have expected : HasDerivAt
      (fun a : ℝ=>stateHamiltonian (sourceVoltageActualState+a • sourceVoltageStateDirection value slope) k)
      (if k=0 then sourceVoltageHamiltonianMatrix value slope sourceVoltageActualState else 0) 0 := by
    simpa only [sourceVoltageHamiltonian_affine,one_smul,id_eq] using affine
  exact generated.unique expected

private theorem filtered_fourier_retained (side edge : Fin 2) :
    (fun frequency=>sourceVoltageFiberProjection (fourier (sourceChargedFilteredPacket side edge) frequency))=ᵐ[volume]
      fourier (sourceChargedFilteredPacket side edge) := by
  have fixed : sourceVoltageFiberProjection.compLpL 2 volume (fourier (sourceChargedFilteredPacket side edge))=
      fourier (sourceChargedFilteredPacket side edge) := by
    rw [←GaugeGreen.constant_fourier]
    exact congrArg FullSpace.fourier (sourceChargedFilteredPacket_retained side edge)
  have generated:=sourceVoltageFiberProjection.coeFn_compLpL (fourier (sourceChargedFilteredPacket side edge))
  rw [fixed] at generated
  exact generated.symm

def sourceChargedVoltageOverlap (shift : Position) (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  inner ℂ (sourceChargedFilteredPacket sideL edgeL) (PacketNoise.phaseShift shift (sourceChargedFilteredPacket sideR edgeR))

/-- The actual filtered source legs read the voltage coefficient; the full scalar insertion disappears only in this pairing. -/
theorem sourceChargedVoltageEnergy_actual (value slope : ℝ) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedEnergyRead (sourceVoltageStateDirection value slope) shift sideL edgeL sideR edgeR=
      (value:ℂ)*sourceChargedVoltageOverlap shift sideL edgeL sideR edgeR := by
  have shifted:=(measurePreserving_sub_right volume shift).quasiMeasurePreserving.ae
    (filtered_fourier_retained sideR edgeR)
  rw [sourceChargedEnergyRead_fourier]
  simp only [sourceVoltageEnergyJet_coefficients,affineMatrix,ite_true,Fin.succ_ne_zero,ite_false,
    smul_zero,Finset.sum_const_zero,add_zero]
  calc
    _=∫frequency : Position,(value:ℂ)*inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
        (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift)) := by
      apply integral_congr_ae
      filter_upwards [filtered_fourier_retained sideL edgeL,shifted] with frequency left right
      exact sourceVoltageHamiltonian_pair sourceVoltageActualState (PreparationVacuumNonlinearFieldCurve.sourceState_valid sourcePoint).2
        value slope _ _ left right
    _=(value:ℂ)*sourceChargedVoltageOverlap shift sideL edgeL sideR edgeR := by
      rw [integral_const_mul,sourceChargedVoltageOverlap,←fourier.inner_map_map,L2.inner_def,
        PacketNoise.phaseShift_fourier]
      congr 1
      apply integral_congr_ae
      filter_upwards [PacketNoise.frequencyShift_ae shift (fourier (sourceChargedFilteredPacket sideR edgeR))] with frequency read
      rw [read]

end LowEnergy.PreparationPhysicalVoltageEnergyIdentity
