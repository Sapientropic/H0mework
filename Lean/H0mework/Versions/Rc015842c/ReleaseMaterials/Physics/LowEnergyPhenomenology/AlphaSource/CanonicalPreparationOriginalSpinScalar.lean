import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationGaugeCurvatureMixed

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumLorentzFieldInjection
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineDynamicBreakingVacuum SU7MotherLieAlgebra DiracExteriorMatterAction DiracCliffordRepresentation
open SU7ExteriorBreakingYukawa SU7ExteriorMatterRepresentation StageNineDiracDualYukawaSpinJurisdiction
open PointwiseDiracSpinConnectionLift StageNineLorentzConnectionVariation
open FullQuantum.StateGreen FullQuantum.CoframeResponse SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates GaussNativeMatter GaussHistoryHilbert
open PreparationVacuumGaugeSourceInjection PreparationVacuumSourceFieldFamily
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumNonlinearFieldCurve
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional

def lorentzGenerator (a : Fin 6) : PointwiseLorentzSpinConnection:=
  lorentzSkewConnectionOfBivectorOneForm (Pi.single 0 (Pi.single a 1))

def spinGenerator (a : Fin 6) : DiracMatrix:=diracSpinConnectionLift (lorentzGenerator a) 0

def frameGenerator (a : Fin 6) : LorentzianCoframe:=lorentzGenerator a 0

 theorem spinGenerator_original (a : Fin 6) :
    spinCoordinates (spinGenerator a)=nativeMatterGenerator (Fin.natAdd 3 a) :=by
  rw [nativeMatterGenerator_spin_original]
  rfl

 theorem frameGenerator_original (a : Fin 6) : frameGenerator a=nativeFrameGenerator (Fin.natAdd 3 a) :=by
  rw [nativeFrameGenerator_spin_original]
  rfl

 theorem originalSpin_repairedYukawa (omega : PointwiseLorentzSpinConnection) (mu : Fin 4)
    (phi : ExteriorBreakingScalarCarrier) (v : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (diracSpinConnectionLift omega mu) (diracDualRightChiralYukawaAction phi v)=
      diracDualRightChiralYukawaAction phi (diracMatrixMatterAction (diracSpinConnectionLift omega mu) v) :=by
  unfold diracDualRightChiralYukawaAction
  simp only [LinearMap.comp_apply]
  have inside:=LinearMap.congr_fun (diracMatrixMatterAction_commutes_internal
    (diracSpinConnectionLift omega mu) (exteriorYukawaInternalAction phi))
    (diracMatrixMatterAction rightChiralityProjector v)
  simp only [LinearMap.comp_apply] at inside
  change diracMatrixMatterAction (diracSpinConnectionLift omega mu)
    (internalMatterLinearAction (exteriorYukawaInternalAction phi)
      (diracMatrixMatterAction rightChiralityProjector v))=_
  rw [inside,diracMatrixMatterAction_apply_apply,diracSpinConnectionLift_preserves_rightChirality,
    ←diracMatrixMatterAction_apply_apply]
  rfl

 theorem originalSpin_scalar_commutator (omega : PointwiseLorentzSpinConnection) (mu : Fin 4) (phi : Scalar) :
    spinCoordinates (diracSpinConnectionLift omega mu)*scalarLinear phi=
      scalarLinear phi*spinCoordinates (diracSpinConnectionLift omega mu) :=by
  change Quantum.operatorMatrix (diracMatrixMatterAction (diracSpinConnectionLift omega mu))*
    Quantum.operatorMatrix (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm phi))=
      Quantum.operatorMatrix (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm phi))*
        Quantum.operatorMatrix (diracMatrixMatterAction (diracSpinConnectionLift omega mu))
  rw [←Quantum.matrix_composition,←Quantum.matrix_composition]
  apply congrArg Quantum.operatorMatrix
  apply LinearMap.ext
  intro v
  exact originalSpin_repairedYukawa omega mu _ v

 theorem spinScalar_direction_original (a : Fin 6) (theta : ℝ) (phi : Scalar) :
    scalarLinear (0:Scalar)=theta • (nativeMatterGenerator (Fin.natAdd 3 a)*scalarLinear phi-
      scalarLinear phi*nativeMatterGenerator (Fin.natAdd 3 a)) :=by
  rw [←spinGenerator_original]
  have source : spinCoordinates (spinGenerator a)*scalarLinear phi=scalarLinear phi*spinCoordinates (spinGenerator a):=
    originalSpin_scalar_commutator (lorentzGenerator a) 0 phi
  rw [source,sub_self,smul_zero,map_zero]

 theorem spinGauge_direction_original (a : Fin 6) (A : NativeLie) :
    nativeMatterGenerator (Fin.natAdd 3 a)*nativePrimal A-nativePrimal A*nativeMatterGenerator (Fin.natAdd 3 a)=0 :=by
  rw [←spinGenerator_original,originalSpin_internal_commute,sub_self]

end LowEnergy.PreparationVacuumLorentzFieldInjection
