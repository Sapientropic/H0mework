import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparationResidual

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.ActualPreparedPiPreparationReturnProducer

open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussHistoryHilbert GaussComposite.SourceGraph
open CanonicalGradedSpatialSource
open PreparationVacuumSourcePreparedState PreparationVacuumSourcePreparedResponse
open PreparationVacuumNativeClosure PreparationVacuumLocalizedYukawa PreparationVacuumPreparedCurrent
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalScalarPreparation
open PreparationChartGuard
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedPreparationEnergy
open GaussComposite.PhysicalEMDressedCharacter
open ActualDressedJointGraph
open scoped Topology InnerProductSpace BigOperators Matrix LinearPMap
local instance : NormedAddCommGroup ScalarZero := inferInstance
local instance : NormedAddCommGroup sourceLocalSpace := inferInstance
local instance : InnerProductSpace ℂ ScalarZero := inferInstance
local instance : CompleteSpace ScalarZero := inferInstance

/-- The actual preparation occurrence carried into the dressed event.  The fields retain
both transported endpoints and their source-generated residuals; no Pi, C_EM, or
experimental value is inserted. -/
structure ActualPreparedPiPreparationReturn (event : DressedEvent) where
  point : sourceOperator.domain
  point_from_source : point = (sourcePreparation event.epsilon event.precision).point
  preparationResidual : sourceLocalSpace
  preparationResidual_from_source :
    preparationResidual = ActualDressedPreparationEnergy.preparationResidual event
  preparationResidual_bound : ‖preparationResidual‖ < event.epsilon
  preparedBackground : H
  preparedBackground_from_source :
    preparedBackground = prepared (sourceProfile event.epsilon event.precision)
  background_transport : sourcePrepared point.val = preparedBackground
  background_residual :
    ‖sourcePrepared (sourceOperator point) -
      (sourceEnergy : ℂ) • preparedBackground‖ < event.epsilon
  creationMap : sourceLocalSpace →L[ℂ] H
  creationMap_from_source : creationMap = preparationCreationMap event
  actualUnit : H
  actualUnit_from_source : actualUnit = sourceDressedUnit event.epsilon event.precision
  creation_transport : creationMap point.val = actualUnit
  creation_normalizer : ‖(‖sourceDressedExcitation event.epsilon event.precision‖ : ℂ)⁻¹ *
      emDressedCharacter true‖ ≤ 2
  creation_residual :
    ‖creationMap (sourceOperator point) -
      (sourceEnergy : ℂ) • actualUnit‖ ≤
      (2 * ‖sourceLeg true 1 0‖) * event.epsilon

variable (event : DressedEvent)

/-- The same source preparation point constructs the full return without a caller-owned
state or an externally supplied compatibility equality. -/
def ActualPreparedPiPreparationReturn.of_source :
    ActualPreparedPiPreparationReturn event := by
  let point := (sourcePreparation event.epsilon event.precision).point
  let residual := ActualDressedPreparationEnergy.preparationResidual event
  refine ⟨point, rfl, residual, rfl, ?_, prepared (sourceProfile event.epsilon event.precision), rfl,
    ?_, ?_, preparationCreationMap event, rfl, sourceDressedUnit event.epsilon event.precision, rfl,
    ?_, ?_, ?_⟩
  · exact preparation_residual_price event
  · exact preparation_background event
  · exact preparation_background_residual event
  · exact preparation_creation_actual event
  · exact preparation_creation_normalizer event
  · exact preparation_creation_residual event

 theorem prepared_background_read
    (owner : ActualPreparedPiPreparationReturn event) :
    sourcePrepared owner.point.val = owner.preparedBackground :=
  owner.background_transport

theorem actual_creation_read
    (owner : ActualPreparedPiPreparationReturn event) :
    owner.creationMap owner.point.val = owner.actualUnit :=
  owner.creation_transport

theorem preparation_residual_read
    (owner : ActualPreparedPiPreparationReturn event) :
    ‖owner.preparationResidual‖ < event.epsilon :=
  owner.preparationResidual_bound

theorem background_residual_read
    (owner : ActualPreparedPiPreparationReturn event) :
    ‖sourcePrepared (sourceOperator owner.point) -
      (sourceEnergy : ℂ) • owner.preparedBackground‖ < event.epsilon :=
  owner.background_residual

theorem creation_residual_read
    (owner : ActualPreparedPiPreparationReturn event) :
    ‖owner.creationMap (sourceOperator owner.point) -
      (sourceEnergy : ℂ) • owner.actualUnit‖ ≤
      (2 * ‖sourceLeg true 1 0‖) * event.epsilon :=
  owner.creation_residual

end LowEnergy.GaussComposite.ActualPreparedPiPreparationReturnProducer
