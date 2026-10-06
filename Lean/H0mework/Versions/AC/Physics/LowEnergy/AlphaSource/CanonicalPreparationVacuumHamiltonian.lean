import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationVacuumCore
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFactor
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussCoreHilbert GaussCoreDifferential GaussLiveMomentum GaussDensityCore GaussHistoryHilbert
open GaussQuantumMultiplier GaussNativeEnergy GaussNativePotential GaussNativeForm
open CanonicalPreparationCreation CanonicalPreparationMomentum CanonicalPreparationCore.Completed
open scoped BigOperators ContDiff Distributions
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

def scalarKineticVacuum : ScalarTest →ₗ[ℂ] ScalarTest :=
  (1/2 : ℂ) • ∑ a : ScalarIndex,
    scalarSandwich (scalarDirection a) (scalarDirection a) scalarWeight scalarWeight_smooth

def gaugeKineticVacuum : ScalarTest →ₗ[ℂ] ScalarTest :=
  (1/2 : ℂ) • ∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3,
    scalarSandwich (gaugeDirection i a) (gaugeDirection j a)
      (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)

def nativeVacuum : ScalarTest →ₗ[ℂ] ScalarTest :=
  scalarKineticVacuum+gaugeKineticVacuum+realCoefficient potential potential_smooth

def scalarVacuumAction : ScalarTest →ₗ[ℂ] ScalarTest :=
  nativeVacuum+coframeKinetic 0+
    realCoefficient GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth

theorem scalarKinetic_vacuum (f : ScalarTest) :
    scalarKinetic (vacuumSection f)=vacuumSection (scalarKineticVacuum f) := by
  simp only [scalarKinetic,scalarKineticVacuum,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact sandwich_vacuum _ _ _ _ f

theorem gaugeKinetic_vacuum (f : ScalarTest) :
    gaugeKinetic (vacuumSection f)=vacuumSection (gaugeKineticVacuum f) := by
  simp only [gaugeKinetic,gaugeKineticVacuum,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact sandwich_vacuum _ _ _ _ f

theorem nativeAction_vacuum (f : ScalarTest) :
    nativeAction (vacuumSection f)=vacuumSection (nativeVacuum f) := by
  simp only [nativeAction,nativeVacuum,LinearMap.add_apply,map_add]
  rw [scalarKinetic_vacuum,gaugeKinetic_vacuum,multiply_vacuum]

theorem spinCurrent_vacuum (a : Fin 7) (f : ScalarTest) :
    GaussCoframeSpin.current a (vacuumSection f)=0 :=
  multiplier_vacuum _ _ f

theorem mixed_vacuum (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) (f : ScalarTest) :
    GaussCoframeForm.mixed i a c smooth (vacuumSection f)=0 := by
  simp only [GaussCoframeForm.mixed,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.comp_apply]
  rw [spinCurrent_vacuum,map_zero,map_zero,add_zero]
  simp only [GaussCoframeCore.momentum,LinearMap.smul_apply]
  have derivative : GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)
      (vacuumSection f)=vacuumSection (GaussDensityCore.derivative (GaussCoframeCore.coframeDirection i) f) := by
    apply DFunLike.ext
    intro z
    apply PiLp.ext
    intro word
    have identity := GaussCoframeCore.component_derivative
      (GaussCoframeCore.coframeDirection i) (vacuumSection f) word
    rw [vacuum_component,map_smul] at identity
    have value := congrArg (fun g : ScalarTest => g z) identity
    exact value.trans (mul_comm _ _)
  rw [derivative,map_smul,multiply_vacuum,map_smul,spinCurrent_vacuum,smul_zero,smul_zero]

theorem coframeCurrent_vacuum (f : ScalarTest) : GaussCoframeForm.currentAction (vacuumSection f)=0 := by
  simp only [GaussCoframeForm.currentAction,LinearMap.add_apply,mixed_vacuum,add_zero]

theorem spinSquare_vacuum (a : Fin 7) (f : ScalarTest) :
    GaussCoframeForm.spinSquare a (vacuumSection f)=0 := by
  simp only [GaussCoframeForm.spinSquare,LinearMap.smul_apply,LinearMap.comp_apply,
    spinCurrent_vacuum,map_zero,smul_zero]

theorem coframeAction_vacuum (f : ScalarTest) :
    GaussCoframeForm.coframeAction (vacuumSection f)=vacuumSection
      ((coframeKinetic 0+realCoefficient GaussCoframeForm.volumePotential
        GaussCoframeForm.volumePotential_smooth) f) := by
  simp only [GaussCoframeForm.coframeAction,LinearMap.add_apply,LinearMap.sum_apply,
    original_vacuum_kinetic,coframeCurrent_vacuum,spinSquare_vacuum,
    Finset.sum_const_zero,CanonicalPreparationSpin.numberShift_vacuum,
    multiply_vacuum,add_zero,map_add]

theorem matterAction_vacuum (f : ScalarTest) : GaussMatterCore.matterAction (vacuumSection f)=0 := by
  simp only [GaussMatterCore.matterAction,LinearMap.sum_apply,multiplier_vacuum,Finset.sum_const_zero]

theorem originalY_vacuum (f : ScalarTest) : GaussYukawaOperator.originalAction (vacuumSection f)=0 := by
  apply DFunLike.ext
  intro z
  change GaussYukawaCoefficient.sourceMap (scalarField z) (f z • vacuumFiber)=0
  rw [GaussYukawaCoefficient.source_map_return,map_smul,quantized_vacuum,smul_zero]

theorem originalYsharp_vacuum (f : ScalarTest) : GaussFullHamiltonian.adjointAction (vacuumSection f)=0 := by
  apply DFunLike.ext
  intro z
  change (GaussYukawaCoefficient.sourceMap (scalarField z)).adjoint (f z • vacuumFiber)=0
  rw [GaussYukawaCoefficient.source_map_return,map_smul,adjoint_vacuum,smul_zero]

theorem diagonalAction_vacuum (f : ScalarTest) :
    GaussDiagonalHistory.diagonalAction (vacuumSection f)=vacuumSection (scalarVacuumAction f) := by
  simp only [GaussDiagonalHistory.diagonalAction,LinearMap.add_apply,nativeAction_vacuum,
    coframeAction_vacuum,matterAction_vacuum,add_zero,scalarVacuumAction,map_add]
  simp only [add_assoc]

theorem fullAction_vacuum (f : ScalarTest) :
    GaussFullHamiltonian.fullAction (vacuumSection f)=vacuumSection (scalarVacuumAction f) := by
  rw [GaussFullHamiltonian.fullAction,LinearMap.add_apply,diagonalAction_vacuum,originalY_vacuum,add_zero]

theorem sharpAction_vacuum (f : ScalarTest) :
    GaussFullHamiltonian.sharpAction (vacuumSection f)=vacuumSection (scalarVacuumAction f) := by
  rw [GaussFullHamiltonian.sharpAction,LinearMap.add_apply,diagonalAction_vacuum,
    originalYsharp_vacuum,add_zero]

theorem source_measure_pair (f g : ScalarTest) :
    GaussFockPair.sourcePair (vacuumSection f) (vacuumSection g)=
      inner ℂ (zeroCore f) (zeroCore g) := by
  change inner ℂ (embed (vacuumSection f)) (embed (vacuumSection g))=_
  rw [PiLp.inner_apply]
  change (∑ word : Occupation, inner ℂ
    (scalarLp word.card (component word (vacuumSection f)))
    (scalarLp word.card (component word (vacuumSection g))))=_
  have terms (word : Occupation) :
      inner ℂ (scalarLp word.card (component word (vacuumSection f)))
        (scalarLp word.card (component word (vacuumSection g)))=
      if word=∅ then inner ℂ (zeroCore f) (zeroCore g) else 0 := by
    rw [vacuum_component,vacuum_component,GaussComposite.SourceGraph.scalarLp_smul,
      GaussComposite.SourceGraph.scalarLp_smul]
    by_cases empty : word=∅
    · subst word
      rw [vacuumFiber_single]
      change inner ℂ ((1 : ℂ) • scalarLp 0 f) ((1 : ℂ) • scalarLp 0 g)=
        if (∅ : Occupation)=∅ then inner ℂ (zeroCore f) (zeroCore g) else 0
      simp only [one_smul,ite_true]
      rfl
    · have zero : vacuumFiber word=0 := by
        rw [vacuumFiber_single]
        simp [EuclideanSpace.single,empty]
      simp [zero,empty]
  simp_rw [terms]
  simp

theorem scalarVacuumAction_pair (f g : ScalarTest) :
    inner ℂ (zeroCore f) (zeroCore (scalarVacuumAction g))=
      inner ℂ (zeroCore (scalarVacuumAction f)) (zeroCore g) := by
  have pair := GaussFullHamiltonian.full_action_pair (vacuumSection f) (vacuumSection g)
  rw [fullAction_vacuum,sharpAction_vacuum,source_measure_pair,source_measure_pair] at pair
  exact pair

end LowEnergy.PreparationVacuumFactor
