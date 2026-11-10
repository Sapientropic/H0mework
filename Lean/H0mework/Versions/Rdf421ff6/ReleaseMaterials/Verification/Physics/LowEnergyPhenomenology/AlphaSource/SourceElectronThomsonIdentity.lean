import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceElectronStaticConsumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceThomsonStaticResponse

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalElectronThomsonIdentity
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open CanonicalGradedSpatialSource
open GaussUnitaryHistory (Index)
open PreparationPhysicalElectronChargeUnitReturn
open PreparationPhysicalThomsonMatchingReturn
open PreparationPhysicalStaticCompositeProjectionReturn
open PreparationVacuumFieldCovector
open PreparationVacuumFieldConstraintResponse
open PreparationVacuumStaticPoleResponse
open PreparationVacuumSourcePreparedResponse
open PreparationPhysicalDressedPhotonCouplingReturn
open CanonicalPhysicalYResolvent
open PreparationVacuumPhysicalPoleSheet
open PreparationPhysicalPhaseGaugeRealization
open SourceQuantumResidualGaugeSlice
open GaussComposite
open GaussComposite.SourceGraph
open PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFieldConstraintResponse
open scoped BigOperators Matrix Topology InnerProductSpace

/-! This is the first direct source identity between the actual electron column and
the static coefficient handed to the Thomson matching owner.  The two sides use
the same prepared external legs and the same full static residue. -/

structure SourceElectronThomsonSetup where
  sideD : Fin 2
  sideS : Fin 2
  epsD : ℝ
  precD : 0 < epsD
  pD : PhysicalMomentum
  kD : PhysicalMomentum
  FD : Index
  cutD : ℕ
  zD : ℂ
  wD : ℂ
  lD : Bool
  rD : Bool
  aD : Fin 2
  sD : Fin 2
  bD : Fin 2
  tD : Fin 2
  epsS : ℝ
  precS : 0 < epsS
  pS : PhysicalMomentum
  kS : PhysicalMomentum
  FS : Index
  cutS : ℕ
  zS : ℂ
  wS : ℂ
  lS : Bool
  rS : Bool
  aS : Fin 2
  sS : Fin 2
  bS : Fin 2
  tS : Fin 2
  branch : Fin 2

def sourceElectronThomsonBareResidue (setup : SourceElectronThomsonSetup) : ℂ :=
  ∑i,preparedCovector setup.epsD setup.precD setup.pD setup.kD setup.FD setup.cutD
      setup.zD setup.wD setup.lD setup.rD setup.aD setup.sD setup.bD setup.tD i*
    staticResidue (preparedCovector setup.epsS setup.precS setup.pS setup.kS setup.FS setup.cutS
      setup.zS setup.wS setup.lS setup.rS setup.aS setup.sS setup.bS setup.tS) i

def sourceElectronThomsonCEM (setup : SourceElectronThomsonSetup) : ℂ :=
  sourceElectronStaticResidueRead setup.sideD setup.sideS
    setup.epsD setup.precD setup.pD setup.kD setup.FD setup.cutD
    setup.zD setup.wD setup.lD setup.rD setup.aD setup.sD setup.bD setup.tD
    setup.epsS setup.precS setup.pS setup.kS setup.FS setup.cutS
    setup.zS setup.wS setup.lS setup.rS setup.aS setup.sS setup.bS setup.tS

def sourceElectronThomsonAlphaSource (setup : SourceElectronThomsonSetup) : ℂ :=
  ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed setup.branch:ℝ):ℂ)⁻¹ *
    sourceElectronThomsonCEM setup

theorem sourceElectronThomson_actual_direction :
    sourcePhaseGaugeLie =
      -SourceQuantumResidualGaugeSlice.colorGenerator 2-(1/2:ℝ) • nativeY :=
  sourceElectron_actual_generator_direction

theorem sourceElectronThomson_charge_unit :
    sourceElectronChargeUnit = 1 :=
  sourceElectronChargeUnit_generated

theorem sourceElectronThomson_normalizer_ne_zero (setup : SourceElectronThomsonSetup) :
    ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed setup.branch:ℝ):ℂ) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr
    (mul_pos Stage10.ActionNormalization.phaseMomentum_positive
      (sourceSpeed_positive setup.branch)).ne'

theorem sourceElectronThomsonCEM_generated (setup : SourceElectronThomsonSetup) :
    sourceElectronThomsonCEM setup =
      -((9/125+67/72:ℂ)*rootTwo*rootFifteen)*
        ((3/10:ℂ)*rootTwo*sourceStaticCompositeConfiguration setup.pD
          (sourceTestApprox setup.FD ((finiteFull (setup.pD+setup.kD) setup.FD setup.cutD
            setup.zD).adjoint
            (completedLeg setup.lD setup.aD setup.sD (sourceProfile setup.epsD setup.precD))))
          (sourceTestApprox setup.FD (finiteFull setup.pD setup.FD setup.cutD setup.wD
            (completedLeg setup.rD setup.bD setup.tD (sourceProfile setup.epsD setup.precD))))) *
        ((3/10:ℂ)*rootTwo*sourceStaticCompositeConfiguration setup.pS
          (sourceTestApprox setup.FS ((finiteFull (setup.pS+setup.kS) setup.FS setup.cutS
            setup.zS).adjoint
            (completedLeg setup.lS setup.aS setup.sS (sourceProfile setup.epsS setup.precS))))
          (sourceTestApprox setup.FS (finiteFull setup.pS setup.FS setup.cutS setup.wS
            (completedLeg setup.rS setup.bS setup.tS (sourceProfile setup.epsS setup.precS))))) := by
  exact sourceElectronStaticResidue_generated setup.sideD setup.sideS
    setup.epsD setup.precD setup.pD setup.kD setup.FD setup.cutD
    setup.zD setup.wD setup.lD setup.rD setup.aD setup.sD setup.bD setup.tD
    setup.epsS setup.precS setup.pS setup.kS setup.FS setup.cutS
    setup.zS setup.wS setup.lS setup.rS setup.aS setup.sS setup.bS setup.tS

theorem sourceElectronThomsonCEM_eq_sourceThomsonStaticCEM (setup : SourceElectronThomsonSetup) :
    sourceElectronThomsonCEM setup =
      sourceThomsonStaticCEM
        setup.epsD setup.precD setup.pD setup.kD setup.FD setup.cutD
        setup.zD setup.wD setup.lD setup.rD setup.aD setup.sD setup.bD setup.tD
        setup.epsS setup.precS setup.pS setup.kS setup.FS setup.cutS
        setup.zS setup.wS setup.lS setup.rS setup.aS setup.sS setup.bS setup.tS := by
  unfold sourceElectronThomsonCEM sourceElectronStaticResidueRead sourceThomsonStaticCEM
  rw [sourceElectronNoetherUnit_generated, sourceElectronNoetherUnit_generated,
    sourceElectronChargeUnit_generated]
  simp

theorem sourceElectronThomsonCEM_eq_bare_residue (setup : SourceElectronThomsonSetup) :
    sourceElectronThomsonCEM setup = sourceElectronThomsonBareResidue setup := by
  unfold sourceElectronThomsonCEM sourceElectronThomsonBareResidue sourceElectronStaticResidueRead
  rw [sourceElectronNoetherUnit_generated, sourceElectronNoetherUnit_generated, sourceElectronChargeUnit_generated]
  simp

theorem sourceElectronThomsonAlpha_eq_matching (setup : SourceElectronThomsonSetup) :
    sourceElectronThomsonAlphaSource setup =
      sourceThomsonAlphaSource setup.branch
        setup.epsD setup.precD setup.pD setup.kD setup.FD setup.cutD
        setup.zD setup.wD setup.lD setup.rD setup.aD setup.sD setup.bD setup.tD
        setup.epsS setup.precS setup.pS setup.kS setup.FS setup.cutS
        setup.zS setup.wS setup.lS setup.rS setup.aS setup.sS setup.bS setup.tS := by
  unfold sourceElectronThomsonAlphaSource sourceThomsonAlphaSource
  rw [sourceElectronThomsonCEM_eq_sourceThomsonStaticCEM]

theorem sourceElectronThomsonCEM_rescale_invariant
    (setup : SourceElectronThomsonSetup) (lambda : ℂ) (hlambda : lambda ≠ 0) :
    (lambda⁻¹ * sourceElectronNoetherUnit setup.sideD) *
        (lambda * sourceElectronNoetherUnit setup.sideD) *
      (lambda⁻¹ * sourceElectronNoetherUnit setup.sideS) *
        (lambda * sourceElectronNoetherUnit setup.sideS) *
        sourceElectronThomsonBareResidue setup = sourceElectronThomsonCEM setup := by
  unfold sourceElectronThomsonBareResidue sourceElectronThomsonCEM
  exact sourceElectronStatic_rescale_invariant setup.sideD setup.sideS lambda hlambda
    setup.epsD setup.precD setup.pD setup.kD setup.FD setup.cutD
    setup.zD setup.wD setup.lD setup.rD setup.aD setup.sD setup.bD setup.tD
    setup.epsS setup.precS setup.pS setup.kS setup.FS setup.cutS
    setup.zS setup.wS setup.lS setup.rS setup.aS setup.sS setup.bS setup.tS

theorem sourceElectronThomsonAlpha_rescale_invariant
    (setup : SourceElectronThomsonSetup) (lambda : ℂ) (hlambda : lambda ≠ 0) :
    ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed setup.branch:ℝ):ℂ)⁻¹ *
      ((lambda⁻¹ * sourceElectronNoetherUnit setup.sideD) *
        (lambda * sourceElectronNoetherUnit setup.sideD) *
        (lambda⁻¹ * sourceElectronNoetherUnit setup.sideS) *
        (lambda * sourceElectronNoetherUnit setup.sideS) *
        sourceElectronThomsonBareResidue setup) =
      sourceElectronThomsonAlphaSource setup := by
  rw [sourceElectronThomsonCEM_rescale_invariant setup lambda hlambda]
  rfl

end LowEnergy.PreparationPhysicalElectronThomsonIdentity
