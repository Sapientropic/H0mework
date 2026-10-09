import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceElectronChargeUnit
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceStaticCompositeCurrent

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalElectronChargeUnitReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalJointEMCouplingUnitReturn
open PreparationPhysicalStaticCompositeProjectionReturn
open FullQuantum FullSpace YangMills.FullPairing
open Stage10 Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource
open PreparationPhysicalCommonCurrentStaticRead
open CanonicalGradedSpatialSource
open GaussUnitaryHistory (Index)
open PreparationVacuumFieldCovector
open PreparationVacuumStaticPoleResponse
open PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFieldConstraintResponse
open PreparationVacuumFullFieldRiesz
open CanonicalPhysicalYResolvent
open GaussComposite.SourceGraph
open PreparationVacuumSourcePreparedResponse
open Electromagnetic.CanonicalCoframe
open scoped BigOperators Matrix Topology InnerProductSpace

/-- The same source-normalized electron units are inserted at both ends of the
already generated static full residue.  The residue remains the complete
field-basis 21−34 response, including all retained configuration terms. -/
def sourceElectronStaticResidueRead
    (sideD sideS : Fin 2)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : GaussUnitaryHistory.Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : GaussUnitaryHistory.Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) : ℂ :=
  sourceElectronNoetherUnit sideD * sourceElectronNoetherUnit sideS *
    (∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*
      staticResidue (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i)

/-- The generated absolute charge units multiply the original static residue
coefficient, with no extra 4π or field normalization. -/
theorem sourceElectronStaticResidue_generated
    (sideD sideS : Fin 2)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : GaussUnitaryHistory.Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : GaussUnitaryHistory.Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) :
    sourceElectronStaticResidueRead sideD sideS epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
      epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS =
      -((9/125+67/72:ℂ)*rootTwo*rootFifteen)*
        ((3/10:ℂ)*rootTwo*sourceStaticCompositeConfiguration pD
          (sourceTestApprox FD ((finiteFull (pD+kD) FD cutD zD).adjoint
            (completedLeg lD aD sD (sourceProfile epsD precD))))
          (sourceTestApprox FD (finiteFull pD FD cutD wD
            (completedLeg rD bD tD (sourceProfile epsD precD))))) *
        ((3/10:ℂ)*rootTwo*sourceStaticCompositeConfiguration pS
          (sourceTestApprox FS ((finiteFull (pS+kS) FS cutS zS).adjoint
            (completedLeg lS aS sS (sourceProfile epsS precS))))
          (sourceTestApprox FS (finiteFull pS FS cutS wS
            (completedLeg rS bS tS (sourceProfile epsS precS))))) := by
  unfold sourceElectronStaticResidueRead
  rw [sourceElectronNoetherUnit_generated, sourceElectronNoetherUnit_generated]
  simpa [sourceElectronChargeUnit_generated] using sourceStaticCompositeLeading_return epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
    epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS

/-- The static charge insertion is unchanged by a common nonzero rescaling of
both source current reads. -/
theorem sourceElectronStatic_rescale_invariant
    (sideD sideS : Fin 2) (lambda : ℂ) (hlambda : lambda ≠ 0)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : GaussUnitaryHistory.Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : GaussUnitaryHistory.Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) :
    (lambda⁻¹ * sourceElectronNoetherUnit sideD) *
      (lambda * sourceElectronNoetherUnit sideD) *
      (lambda⁻¹ * sourceElectronNoetherUnit sideS) *
      (lambda * sourceElectronNoetherUnit sideS) *
      (∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*
        staticResidue (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i)=
    sourceElectronStaticResidueRead sideD sideS epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
      epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS := by
  unfold sourceElectronStaticResidueRead
  simp [sourceElectronNoetherUnit_generated, sourceElectronChargeUnit_generated, hlambda]

end LowEnergy.PreparationPhysicalElectronChargeUnitReturn
