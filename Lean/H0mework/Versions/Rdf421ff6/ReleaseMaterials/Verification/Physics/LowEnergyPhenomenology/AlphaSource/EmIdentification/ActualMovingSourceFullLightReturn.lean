import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualMovingSourceCausalWindow

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.ActualMovingSourceFullLightReturnProducer

open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource SourceQuantumFockGauge
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open ActualMovingSourceLight
open PreparationVacuumActionFieldLift
open ActualDressedFullCoulomb ActualDressedNoether ActualElectronWholeNoetherObserver
open ActualElectronFullNoetherMixedSoft ActualCompositeFieldCurrent
open ActualDressedSylvester
open ActualMixedNoetherTimePriceOwn
open scoped Topology InnerProductSpace Matrix Matrix.Norms.L2Operator BigOperators

/-- The actual light window read, retaining the source contact inside the original observer. -/
def movingLightWindow (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (bits : ℕ) (i j : Fin 289) : ℂ :=
  actualMovingOriginalWindow pL pR reference event transfer lambda
    (originalQuantumHorizon lambda.re bits) i j

/-- The selected heavy I-P read remains a separate source response. -/
def movingHeavyWindow (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (bits : ℕ) (i j : Fin 289) : ℂ :=
  actualMovingHeavyOriginalWindow pL pR reference event transfer lambda
    (originalQuantumHorizon lambda.re bits) i j

/-- The omitted cross/outside arm is retained rather than averaged into the light term. -/
def movingCrossOutsideWindow (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (bits : ℕ) (i j : Fin 289) : ℂ :=
  actualCrossOutsideOriginalWindow event transfer lambda
    (originalQuantumHorizon lambda.re bits) i j

/-- Finite-horizon quantum tail from the original full source response. -/
def movingQuantumTail (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (bits : ℕ) (i j : Fin 289) : ℂ :=
  dressedStaticPolarization event transfer lambda i j -
    originalQuantumBinaryWindow event transfer lambda bits i j

/-- Source-owned full-minus-light return, with the complete non-light arms and quantum tail visible. -/
structure ActualMovingSourceFullLightReturn
    (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ)
    (bits : ℕ) (i j : Fin 289) where
  ordinaryFull : ℂ
  ordinaryFull_from_source : ordinaryFull = dressedStaticPolarization event transfer lambda i j
  lightResponse : ℂ
  lightResponse_from_source : lightResponse = movingLightWindow pL pR reference event transfer lambda bits i j
  heavyResponse : ℂ
  heavyResponse_from_source : heavyResponse = movingHeavyWindow pL pR reference event transfer lambda bits i j
  crossOutsideResponse : ℂ
  crossOutsideResponse_from_source : crossOutsideResponse = movingCrossOutsideWindow event transfer lambda bits i j
  quantumTail : ℂ
  quantumTail_from_source : quantumTail = movingQuantumTail event transfer lambda bits i j
  full_light_partition : ordinaryFull - lightResponse =
    heavyResponse + crossOutsideResponse + quantumTail

variable {pL pR : PhysicalMomentum} {reference : SourceCoordinateSlice}
  {event : DressedEvent} {transfer : PhysicalMomentum} {lambda : ℂ}
  {bits : ℕ} {i j : Fin 289}

/-- The three source arms and the finite quantum tail exhaust the full source read. -/
theorem actualMovingSourceFullLightReturn_partition
    (owner : ActualMovingSourceFullLightReturn pL pR reference event transfer lambda bits i j) :
    owner.ordinaryFull - owner.lightResponse =
      owner.heavyResponse + owner.crossOutsideResponse + owner.quantumTail :=
  owner.full_light_partition

def ActualMovingSourceFullLightReturn.of_source
    (pL pR : PhysicalMomentum) (reference : SourceCoordinateSlice)
    (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ)
    (bits : ℕ) (i j : Fin 289) : ActualMovingSourceFullLightReturn pL pR reference event transfer lambda bits i j := by
  refine ⟨dressedStaticPolarization event transfer lambda i j, rfl,
    movingLightWindow pL pR reference event transfer lambda bits i j, rfl,
    movingHeavyWindow pL pR reference event transfer lambda bits i j, rfl,
    movingCrossOutsideWindow event transfer lambda bits i j, rfl,
    movingQuantumTail event transfer lambda bits i j, rfl, ?_⟩
  have partition := actual_original_quantum_binary_moving_partition pL pR reference event transfer lambda bits i j
  unfold movingLightWindow movingHeavyWindow movingCrossOutsideWindow movingQuantumTail
  rw [partition]
  ring

/-- The source tail has the independently paid binary-horizon bound. -/
theorem actualMovingSourceFullLightReturn_tail_bound
    (owner : ActualMovingSourceFullLightReturn pL pR reference event transfer lambda bits i j)
    (positive : 0 < lambda.re) (small : lambda.re ≤ 2) :
    ‖owner.quantumTail‖ ≤
      (896 * sourceCompleteCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j) /
        lambda.re^4) * (1 / 2 : ℝ)^bits := by
  rw [owner.quantumTail_from_source, movingQuantumTail]
  exact actualFullQuantum_binary_source_error event transfer lambda positive small bits i j

/-- The source full-minus-light error keeps the heavy/cross arm and the finite tail separate. -/
theorem actualMovingSourceFullLightReturn_error
    (owner : ActualMovingSourceFullLightReturn pL pR reference event transfer lambda bits i j)
    (positive : 0 < lambda.re) (small : lambda.re ≤ 2) :
    ‖owner.ordinaryFull - owner.lightResponse‖ ≤
      (896 * sourceCompleteCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j) /
        lambda.re^4) * (1 / 2 : ℝ)^bits +
      ‖owner.heavyResponse + owner.crossOutsideResponse‖ := by
  rw [owner.ordinaryFull_from_source, owner.lightResponse_from_source,
    owner.heavyResponse_from_source, owner.crossOutsideResponse_from_source,
    movingLightWindow]
  exact actual_moving_source_light_window_error pL pR reference event transfer lambda positive small bits i j

end LowEnergy.GaussComposite.ActualMovingSourceFullLightReturnProducer
