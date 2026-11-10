import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMPhaseField
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMTemporalGerm
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedLeftFreeJet
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3RawEMReader
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedActionPhase
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSignedWeightTorque

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMWeightedTorque
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open GaussHistoryHilbert
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussQuantumMultiplier
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open CanonicalGradedSpatialSource CanonicalGradedCharge CanonicalPhysicalSpatial CanonicalPhysicalWardCore
open PreparationVacuumJointFieldResponse
open PreparationVacuumGradedTransport PreparationVacuumMixedFieldReturn
open PreparationVacuumActualFieldQuantization
open PreparationVacuumActionFieldLift PreparationVacuumNoetherChart PreparationVacuumFullFieldRiesz
open PreparationPhysicalFirstTemporalChargeReturn PreparationPhysicalSignedVolumeWeightReturn
open PreparationVacuumWeightedChargeActionWard
open PreparationPhysicalSignedWeightDynamics PreparationPhysicalPhaseGaugeRealization
open PreparationVacuumUncutYukawa ActualDressedEMTemporal ActualDressedActionPhase
open ActualSourcePreparedEMPhaseField ActualDressedLeftFreeJet PhysicalN3SourceEnergy PhysicalEMVoltage
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := Classical.decEq _
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _
attribute [local irreducible] jointCompression emTemporalReader sourceSignedVolumeReader

def sourceEMTemporalCore : QuantumTest →ₗ[ℂ] QuantumTest :=
  sourceTemporalMatrixCore emGaugeChargeMatrix

/-- The original momentum-weighted CAR reader is exactly the original
signed-volume reader on the same finite frame. -/
theorem source_em_temporal_signed_reader (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    emTemporalReader p F = sourceSignedVolumeReader emGaugeChargeMatrix F := by
  unfold emTemporalReader
  rw [← source_em_phase_field]
  exact physical_n3_noether_em_signed_volume p F

/-- The CAR pair term remains in the source operator, before finite compression. -/
theorem source_em_temporal_core_full_car :
    sourceEMTemporalCore = weightCore.comp (chargeAction sourcePhaseGaugeLie) -
      sourceTemporalNormalCore emGaugeChargeMatrix := by
  rw [sourceEMTemporalCore,sourceTemporalNormalCore,em_noether_matrix_same]
  change _ = weightCore.comp (chargeAction sourcePhaseGaugeLie) -
    (weightCore.comp (chargeAction sourcePhaseGaugeLie) - sourceTemporalMatrixCore _)
  abel

private theorem signed_charge_commutes :
    sourceTimeSignMatrix * emGaugeChargeMatrix = emGaugeChargeMatrix * sourceTimeSignMatrix := by
  rw [em_noether_matrix_same,chargeMatrix,mul_smul_comm,smul_mul_assoc,sourceTimeSign_native]

private theorem source_em_symbol_hermitian (z : physicalChart) :
    (sourceWeightSymbol z.val * emGaugeChargeMatrix).conjTranspose =
      sourceWeightSymbol z.val * emGaugeChargeMatrix := by
  rw [sourceWeightSymbol_signed,smul_mul_assoc,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul,sourceTimeSign_hermitian,em_charge_matrix_hermitian,
    Complex.star_def,Complex.conj_ofReal,signed_charge_commutes]

/-- The source measure retains its actual configuration volume. Hermiticity
is generated on that same chart; no caller matrix or normalizer is supplied. -/
theorem source_em_temporal_core_pair (f g : QuantumTest) :
    sourcePair f (sourceEMTemporalCore g) = sourcePair (sourceEMTemporalCore f) g := by
  rw [sourcePair_integral,sourcePair_integral]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  by_cases inside : z ∈ tsupport f
  · have chart : z ∈ physicalChart := f.tsupport_subset inside
    change inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z) (f z))
        (quantized (sourceWeightSymbol z * emGaugeChargeMatrix) (g z)) =
      inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z)
        (quantized (sourceWeightSymbol z * emGaugeChargeMatrix) (f z))) (g z)
    exact weighted_pair _ _ (source_em_symbol_hermitian ⟨z,chart⟩) _ _
  · have zero : f z = 0 := image_eq_zero_of_notMem_tsupport inside
    change inner ℂ (GaussFockWeights.weight _ (f z)) (quantized _ (g z)) =
      inner ℂ (GaussFockWeights.weight _ (quantized _ (f z))) (g z)
    simp only [zero,map_zero,inner_zero_left]

/-- The real source dilation and the exact charge/configuration and CAR
normal commutators are kept as separate native contributions. -/
def sourceEMPhysicalCoreTorque (p : PhysicalMomentum) : QuantumTest →ₗ[ℂ] QuantumTest :=
  ((Stage10.ActionNormalization.phaseMomentum : ℂ) •
    (((-3*Complex.I*(GaussNativeEnergy.sourceTime 0 : ℂ)/4) • SourceCoframeVolumeCurrent.dilation).comp
      sourceTimeSignCore)).comp (chargeAction sourcePhaseGaugeLie) +
    weightCore.comp (configurationTorque sourcePhaseGaugeLie) -
    ((physicalAction p).comp (sourceTemporalNormalCore emGaugeChargeMatrix) -
      (sourceTemporalNormalCore emGaugeChargeMatrix).comp (physicalAction p))

private theorem physical_charge_residual (p : PhysicalMomentum) :
    (physicalAction p).comp (chargeAction sourcePhaseGaugeLie) -
      (chargeAction sourcePhaseGaugeLie).comp (physicalAction p) =
        configurationTorque sourcePhaseGaugeLie := by
  have commute := (momentum_charge_commutes p sourcePhaseGaugeLie).eq
  change momentumAction p * chargeAction sourcePhaseGaugeLie =
    chargeAction sourcePhaseGaugeLie * momentumAction p at commute
  change (GaussDiagonalHistory.diagonalAction+momentumAction p)*chargeAction sourcePhaseGaugeLie-
      chargeAction sourcePhaseGaugeLie*(GaussDiagonalHistory.diagonalAction+momentumAction p)=_
  simp only [add_mul,mul_add,commute]
  change _ = GaussDiagonalHistory.diagonalAction*chargeAction sourcePhaseGaugeLie-
    chargeAction sourcePhaseGaugeLie*GaussDiagonalHistory.diagonalAction
  noncomm_ring

/-- The actual weighted EM source operator generates its physical residual.
No commutation, phase eigenstate or zero torque is taken as a premise. -/
theorem source_em_physical_core_torque (p : PhysicalMomentum) :
    (physicalAction p).comp sourceEMTemporalCore - sourceEMTemporalCore.comp (physicalAction p) =
      sourceEMPhysicalCoreTorque p := by
  have weight := sourceWeightCore_physicalTorque p
  have charge := physical_charge_residual p
  rw [source_em_temporal_core_full_car]
  change physicalAction p*(weightCore*chargeAction sourcePhaseGaugeLie-sourceTemporalNormalCore emGaugeChargeMatrix)-
    (weightCore*chargeAction sourcePhaseGaugeLie-sourceTemporalNormalCore emGaugeChargeMatrix)*physicalAction p=_
  have product : physicalAction p*(weightCore*chargeAction sourcePhaseGaugeLie-sourceTemporalNormalCore emGaugeChargeMatrix)-
      (weightCore*chargeAction sourcePhaseGaugeLie-sourceTemporalNormalCore emGaugeChargeMatrix)*physicalAction p =
    (physicalAction p*weightCore-weightCore*physicalAction p)*chargeAction sourcePhaseGaugeLie+
      weightCore*(physicalAction p*chargeAction sourcePhaseGaugeLie-chargeAction sourcePhaseGaugeLie*physicalAction p)-
      (physicalAction p*sourceTemporalNormalCore emGaugeChargeMatrix-sourceTemporalNormalCore emGaugeChargeMatrix*physicalAction p) := by
    noncomm_ring
  rw [product]
  change (physicalAction p).comp weightCore - weightCore.comp (physicalAction p) = _ at weight
  change (physicalAction p).comp (chargeAction sourcePhaseGaugeLie) -
    (chargeAction sourcePhaseGaugeLie).comp (physicalAction p) = _ at charge
  change _ = sourceEMPhysicalCoreTorque p
  rw [show physicalAction p*weightCore-weightCore*physicalAction p = _ from weight,
    show physicalAction p*chargeAction sourcePhaseGaugeLie-chargeAction sourcePhaseGaugeLie*physicalAction p = _ from charge]
  rfl

private theorem actual_physical_pair (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (x y : H) : inner ℂ x (jointCompression p F 0 y) =
      ∑ g : NativeHistoryGrade.Label,
        sourcePair (gradedTest p F g x) (physicalAction p (gradedTest p F g y)) := by
  have paid := (gradedForm_pair (0 : Field289) p F x y).self_of_nhds
  simpa only [gradedForm_zero,physicalForm_source,free_compression_base] using paid

/-- Both actual finite frames are retained; neither restriction is declared
closed under the source EM operator. -/
def sourceEMPhysicalRightDefect (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (g : NativeHistoryGrade.Label) (y : H) : QuantumTest :=
  gradedTest p F g (emTemporalReader p F y) - sourceEMTemporalCore (gradedTest p F g y)

def sourceEMPhysicalLeftDefect (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (g : NativeHistoryGrade.Label) (x : H) : QuantumTest :=
  gradedTest p F g ((emTemporalReader p F).adjoint x) - sourceEMTemporalCore (gradedTest p F g x)

def sourceEMPhysicalCompressionTorque (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (x y : H) : ℂ :=
  ∑ g : NativeHistoryGrade.Label,
    (sourcePair (gradedTest p F g x) (sourceEMPhysicalCoreTorque p (gradedTest p F g y)) +
      sourcePair (gradedTest p F g x) (physicalAction p (sourceEMPhysicalRightDefect p F g y)) -
      sourcePair (sourceEMPhysicalLeftDefect p F g x) (physicalAction p (gradedTest p F g y)))

/-- The actual finite EM reader consumes the original dilation, charge and
CAR residual together with both actual source-frame defects. -/
theorem source_em_physical_compression_torque (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (x y : H) :
    inner ℂ x ((jointCompression p F 0*emTemporalReader p F-
      emTemporalReader p F*jointCompression p F 0) y) = sourceEMPhysicalCompressionTorque p F x y := by
  simp only [sub_apply,mul_apply_eq_comp,inner_sub_right]
  rw [← ContinuousLinearMap.adjoint_inner_left (emTemporalReader p F) (jointCompression p F 0 y) x,
    actual_physical_pair,actual_physical_pair,← Finset.sum_sub_distrib]
  unfold sourceEMPhysicalCompressionTorque
  apply Finset.sum_congr rfl
  intro g _
  have right : gradedTest p F g (emTemporalReader p F y) =
      sourceEMTemporalCore (gradedTest p F g y) + sourceEMPhysicalRightDefect p F g y := by
    unfold sourceEMPhysicalRightDefect;abel
  have left : gradedTest p F g ((emTemporalReader p F).adjoint x) =
      sourceEMTemporalCore (gradedTest p F g x) + sourceEMPhysicalLeftDefect p F g x := by
    unfold sourceEMPhysicalLeftDefect;abel
  rw [right,left]
  have core := LinearMap.congr_fun (source_em_physical_core_torque p) (gradedTest p F g y)
  simp only [LinearMap.sub_apply,LinearMap.comp_apply] at core
  have pair := congrArg (sourcePair (gradedTest p F g x)) core
  simp only [sourcePair,map_sub,inner_sub_right] at pair
  simp only [sourcePair,map_add,inner_add_right,inner_add_left]
  have transpose := source_em_temporal_core_pair (gradedTest p F g x)
    (physicalAction p (gradedTest p F g y))
  change inner ℂ (embed (gradedTest p F g x)) (embed (sourceEMTemporalCore _)) =
    inner ℂ (embed (sourceEMTemporalCore (gradedTest p F g x))) (embed _) at transpose
  rw [← transpose]
  linear_combination pair

end LowEnergy.GaussComposite.ActualSourcePreparedEMWeightedTorque
