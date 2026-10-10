import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePinnedPoleBoundary
set_option autoImplicit false
noncomputable section
namespace IndependentPinnedBoundaryConsumer
open LowEnergy.PreparationVacuumObservedPoleTensor
open LowEnergy.PreparationVacuumPhysicalSlowBlock
open LowEnergy.PreparationVacuumPhysicalPinnedVelocity
example (F : GaussUnitaryHistory.Index) (n : CanonicalGradedSpatialSource.PhysicalMomentum)
    (c eta : ℝ) (positive : 0 < eta) :
    sourcePinnedResolvent F n (sourcePoleSide c eta) =
      (eta : ℂ)⁻¹ • sourceResonanceProjection F n c + sourceOffPoleReturn F n c eta :=
  sourcePinnedResolvent_boundary F n c eta positive
#print axioms sourcePinnedResolvent_boundary
end IndependentPinnedBoundaryConsumer
