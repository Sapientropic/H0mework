import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePinnedPoleBoundary
set_option autoImplicit false
noncomputable section
namespace LowEnergy.IndependentPinnedBoundaryConsumer
open PreparationVacuumObservedPoleTensor
open GaussCoreHilbert GaussUnitaryHistory SourceJointResidualEnergy
open PreparationVacuumPhysicalSlowBlock PreparationVacuumPhysicalPinnedVelocity
open CanonicalGradedSpatialSource
open Filter Set
open scoped BigOperators InnerProductSpace Topology
example (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (c eta : ℝ) (positive : 0<eta) :
    sourcePinnedResolvent F n (sourcePoleSide c eta)=
      (eta:ℂ)⁻¹ • sourceResonanceProjection F n c+sourceOffPoleReturn F n c eta :=
  sourcePinnedResolvent_boundary F n c eta positive
#print axioms sourcePinnedResolvent_boundary
end LowEnergy.IndependentPinnedBoundaryConsumer
