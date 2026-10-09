import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceRestPoleSpectrum
import H0mework.Physics.SpinPair.Adjoint
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceQuantumResidualGaugeSlice

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalElectromagneticDirection
open SaturationMonoid.PhysicsCore DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open SU7ExteriorBreakingYukawa SU7ExteriorMatterGaugeCovariantJet SU7ExteriorMatterRepresentation
open StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineCoframeGravityGaugeRegularity
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumResidualGaugeSlice
open SourceQuantumNativeDimensions SourceQuantumScalarOrbitDimensions
open scoped BigOperators Matrix

def sourceLockedAction (i : Fin 3) : DiracExteriorMatterCarrier→ₗ[ℂ]DiracExteriorMatterCarrier :=
  diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator i))+
    (1/2 : ℂ) • diracMatrixMatterAction (spinRotation i)

theorem sourceLockedAction_primal (i : Fin 3) (u v : ℂ) :
    sourceLockedAction i (spinPairMatter u v)=0 := by
  simp only [sourceLockedAction,LinearMap.add_apply,LinearMap.smul_apply]
  rw [spinPair_generator_action]
  module

private theorem dual_matrix (M : DiracMatrix) (matter : DiracExteriorMatterCarrier)
    (s : DiracSpinorIndex) (c : Fin 2) :
    sourceColorDoubletDual c (diracMatrixMatterAction M matter s)=
      ∑t : DiracSpinorIndex,M s t*sourceColorDoubletDual c (matter t) := by
  change sourceColorDoubletDual c (∑t : DiracSpinorIndex,M s t • matter t)=_
  simp only [map_sum,map_smul,smul_eq_mul]

theorem sourceLockedAction_independentDual (i : Fin 3) (p q : ℂ) (matter : DiracExteriorMatterCarrier) :
    spinPairDual p q (sourceLockedAction i matter)=0 := by
  simp only [sourceLockedAction,LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,smul_eq_mul]
  change (∑s : DiracSpinorIndex,∑c : Fin 2,spinPairCoefficients p q s c*
      sourceColorDoubletDual c
        (exteriorSpinorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator i)) (matter s)))+
    (1/2 : ℂ)*(∑s : DiracSpinorIndex,∑c : Fin 2,spinPairCoefficients p q s c*
      sourceColorDoubletDual c (diracMatrixMatterAction (spinRotation i) matter s))=0
  simp only [sourceColorDoubletDual_generator,dual_matrix]
  fin_cases i <;>
    simp [spinPairCoefficients,sourceColorPauli,spinRotation,diracGamma,
      diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Fin.sum_univ_four,Fin.sum_univ_two] <;> ring

def sourceIndexRotation (i j k : Fin 3) : ℝ :=
  if (i,j,k)=(0,1,2) ∨ (i,j,k)=(1,2,0) ∨ (i,j,k)=(2,0,1) then 1
  else if (i,j,k)=(0,2,1) ∨ (i,j,k)=(1,0,2) ∨ (i,j,k)=(2,1,0) then -1 else 0

private def nativeBracket (a b : NativeLie) : NativeLie := jointP286CoordinateLieBracket a b

theorem sourceGauge_index_locked (i j : Fin 3) :
    nativeBracket (colorGenerator i) (gaugeCoordinates SourceQuantumResidualGaugeSlice.sourceGauge j)+
      ∑k : Fin 3,sourceIndexRotation i j k • gaugeCoordinates SourceQuantumResidualGaugeSlice.sourceGauge k=0 := by
  unfold nativeBracket
  rw [sourceGauge_apply,jointP286CoordinateLieBracket_smul_right,colorGenerator_bracket]
  simp only [sourceGauge_apply]
  fin_cases i <;> fin_cases j <;>
    simp [sourceIndexRotation]

theorem sourceScalar_color_locked (i : Fin 3) : orbit (colorGenerator i)=0 :=
  colorGenerator_mem i

theorem sourceScalar_gauge_fixed_direction (a : stabilizer) : residualOrbit a=0 ↔ a=0 := by
  constructor
  · intro zero
    apply residualOrbit_injective
    simpa only [map_zero] using zero
  · rintro rfl
    exact map_zero _

end LowEnergy.PreparationVacuumPhysicalElectromagneticDirection
