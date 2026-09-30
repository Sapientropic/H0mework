import H0mework.NavierStokes.Accumulation.WholeActionTube
import H0mework.NavierStokes.GeneratedPaths.InfiniteNonlinearNegativeOneTimeBudget
import H0mework.NavierStokes.InitialData.FiniteSupportPhysicalInvariantTrajectory
import H0mework.NavierStokes.Fourier.PuncturedCanonicalGalerkinTarget

/-!
# Source-generated whole action state for finite support

A finite-support whole state generates a finite action carrier consisting of
its original modes and every ordered-pair output.  On that carrier the finite
state below is exactly the complete whole Fourier tangent, including all
off-source nonlinear rows.  It then feeds the exact whole action tube without
a projection residual.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteSupportWholeActionTube

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open ThreeDimensionalVorticityCoefficientWholeActionTube

noncomputable section

/-- Original support plus every quadratic output generated from it. -/
def wholeFiniteSupportActionModes
    (modes : Finset IntegerWavevector) : Finset IntegerWavevector :=
  finiteVorticityPairOutputSupport modes ∪ modes

theorem modes_subset_wholeFiniteSupportActionModes
    (modes : Finset IntegerWavevector) :
    modes ⊆ wholeFiniteSupportActionModes modes :=
  Finset.subset_union_right

theorem pairOutput_subset_wholeFiniteSupportActionModes
    (modes : Finset IntegerWavevector) :
    finiteVorticityPairOutputSupport modes ⊆
      wholeFiniteSupportActionModes modes :=
  Finset.subset_union_left

/-- The nonzero action closure of a punctured radius-`r` cube lies in the
punctured radius-`2r` cube.  Addition is read from the actual ordered-pair
incidence; no support radius is submitted to the action compiler. -/
theorem nonzeroWholeActionClosure_puncturedCube_subset_doubled
    (radius : Nat) :
    (wholeFiniteSupportActionModes
        (puncturedIntegerWaveFrequencyCube radius)).erase 0 ⊆
      puncturedIntegerWaveFrequencyCube (2 * radius) := by
  intro output outputMem
  rw [Finset.mem_erase] at outputMem
  refine Finset.mem_erase.mpr ⟨outputMem.1, ?_⟩
  rw [wholeFiniteSupportActionModes, Finset.mem_union] at outputMem
  rcases outputMem.2 with pairOutput | sourceOutput
  · rw [finiteVorticityPairOutputSupport, Finset.mem_image] at pairOutput
    obtain ⟨pair, pairMem, rfl⟩ := pairOutput
    obtain ⟨firstMem, secondMem⟩ := Finset.mem_product.mp pairMem
    rw [puncturedIntegerWaveFrequencyCube, Finset.mem_erase] at firstMem secondMem
    rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at firstMem secondMem ⊢
    intro coordinate
    have firstCoordinateMem := firstMem.2 coordinate
    have secondCoordinateMem := secondMem.2 coordinate
    rw [Finset.mem_Icc] at firstCoordinateMem secondCoordinateMem ⊢
    simp only [Pi.add_apply]
    constructor <;> omega
  · rw [puncturedIntegerWaveFrequencyCube, Finset.mem_erase] at sourceOutput
    rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at sourceOutput ⊢
    intro coordinate
    have coordinateMem := sourceOutput.2 coordinate
    rw [Finset.mem_Icc] at coordinateMem ⊢
    constructor <;> omega

/-- The finite carrier containing the complete whole action of a supported
state.  Its values are computed by the whole nonlinear row, not supplied by
a caller. -/
def wholeFiniteSupportActionState
    (viscosity : Real)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState (wholeFiniteSupportActionModes modes) fun output =>
    wholeLatticeVorticityFourierTangentAt viscosity state output

@[simp] theorem wholeFiniteSupportActionState_apply
    (viscosity : Real)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    wholeFiniteSupportActionState viscosity modes state output =
      if output ∈ wholeFiniteSupportActionModes modes then
        wholeLatticeVorticityFourierTangentAt viscosity state output
      else 0 := by
  exact finiteComplexVorticityState_apply _ _ _

/-- Every whole tangent row is retained: outside the generated action carrier
both the original state and its quadratic nonlinear output vanish. -/
theorem wholeFiniteSupportActionState_apply_eq_wholeTangent
    (viscosity : Real)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave : IntegerWavevector,
      wave ∉ modes → state wave = 0)
    (output : IntegerWavevector) :
    wholeFiniteSupportActionState viscosity modes state output =
      wholeLatticeVorticityFourierTangentAt viscosity state output := by
  rw [wholeFiniteSupportActionState_apply]
  by_cases outputMem : output ∈ wholeFiniteSupportActionModes modes
  · rw [if_pos outputMem]
  · rw [if_neg outputMem]
    have outputNotPair :
        output ∉ finiteVorticityPairOutputSupport modes :=
      fun outputPair => outputMem (Finset.mem_union_left _ outputPair)
    have outputNotSource : output ∉ modes :=
      fun outputSource => outputMem (Finset.mem_union_right _ outputSource)
    rw [wholeLatticeVorticityFourierTangentAt,
      wholeStateVorticityNonlinearCoefficientAt_eq_zero_of_supported
        modes state supported output outputNotPair,
      supported output outputNotSource, smul_zero, sub_zero]

/-- The generated whole action state is exactly the finite Galerkin
generator on the enlarged action carrier; this is a commuting theorem, not
the definition of the action. -/
theorem wholeFiniteSupportActionState_eq_finiteGenerator
    (viscosity : Real)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave : IntegerWavevector,
      wave ∉ modes → state wave = 0) :
    wholeFiniteSupportActionState viscosity modes state =
      finiteStateVorticityGenerator
        (wholeFiniteSupportActionModes modes) viscosity state := by
  apply lp.ext
  funext output
  rw [wholeFiniteSupportActionState_apply,
    finiteStateVorticityGenerator_apply]
  by_cases outputMem : output ∈ wholeFiniteSupportActionModes modes
  · rw [if_pos outputMem, if_pos outputMem]
    unfold wholeLatticeVorticityFourierTangentAt
    rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
      (wholeFiniteSupportActionModes modes) state]
    intro wave waveNotMem
    exact supported wave fun waveMem =>
      waveNotMem (modes_subset_wholeFiniteSupportActionModes modes waveMem)
  · rw [if_neg outputMem, if_neg outputMem]

/-- The exact action of a transverse finite-support source remains
transverse on its generated carrier. -/
theorem wholeFiniteSupportActionState_transverse
    (viscosity : Real)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave : IntegerWavevector,
      wave ∉ modes → state wave = 0)
    (stateTransverse : WholeStateTransverse state) :
    WholeStateTransverse
      (wholeFiniteSupportActionState viscosity modes state) := by
  rw [wholeFiniteSupportActionState_eq_finiteGenerator
    viscosity modes state supported]
  intro output
  apply finiteStateVorticityGenerator_transverse
  intro wave _waveMem
  exact stateTransverse wave

/-- Exact source-action specialization of the whole affine tube.  Both the
linear and quadratic material rows are generated from the same source state
and its complete whole action. -/
theorem wholeLatticeVorticityFourierTangentAt_affine_exactActionTube
    (viscosity step : Real)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave : IntegerWavevector,
      wave ∉ modes → state wave = 0)
    (stateTransverse : WholeStateTransverse state)
    (output : IntegerWavevector) :
    let action := wholeFiniteSupportActionState viscosity modes state
    wholeLatticeVorticityFourierTangentAt viscosity
        (state + step • action) output =
      action output +
        step • wholeGeneratorLinearizationRow viscosity state action output +
        step ^ 2 • wholeGeneratorQuadraticRow action output := by
  dsimp only
  rw [wholeLatticeVorticityFourierTangentAt_affine_eq_actionTube
    viscosity step state
    (wholeFiniteSupportActionState viscosity modes state)
    stateTransverse
    (wholeFiniteSupportActionState_transverse
      viscosity modes state supported stateTransverse) output]
  rw [wholeFiniteSupportActionState_apply_eq_wholeTangent
    viscosity modes state supported output]

/-! ## Generated local material advance -/

/-- The finite affine material state generated from a source and its exact
whole action. -/
def wholeFiniteSupportAffineActionState
    (viscosity step : Real)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  state + step • wholeFiniteSupportActionState viscosity modes state

theorem wholeFiniteSupportActionState_supported
    (viscosity : Real)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ wholeFiniteSupportActionModes modes) :
    wholeFiniteSupportActionState viscosity modes state wave = 0 := by
  rw [wholeFiniteSupportActionState_apply, if_neg waveNotMem]

theorem wholeFiniteSupportAffineActionState_supported
    (viscosity step : Real)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave : IntegerWavevector,
      wave ∉ modes → state wave = 0)
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ wholeFiniteSupportActionModes modes) :
    wholeFiniteSupportAffineActionState viscosity step modes state wave = 0 := by
  unfold wholeFiniteSupportAffineActionState
  rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    supported wave (fun waveMem =>
      waveNotMem (modes_subset_wholeFiniteSupportActionModes modes waveMem)),
    wholeFiniteSupportActionState_supported
      viscosity modes state wave waveNotMem,
    smul_zero, add_zero]

theorem wholeFiniteSupportAffineActionState_transverse
    (viscosity step : Real)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave : IntegerWavevector,
      wave ∉ modes → state wave = 0)
    (stateTransverse : WholeStateTransverse state) :
    WholeStateTransverse
      (wholeFiniteSupportAffineActionState viscosity step modes state) := by
  unfold wholeFiniteSupportAffineActionState
  exact wholeStateTransverse_add _ _ stateTransverse
    (wholeStateTransverse_real_smul step _
      (wholeFiniteSupportActionState_transverse
        viscosity modes state supported stateTransverse))

/-- The next exact whole action generated from the affine material state.
The support is advanced locally from `modes` to its action carrier; no stage
table is stored. -/
def wholeFiniteSupportAffineNextActionState
    (viscosity step : Real)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  wholeFiniteSupportActionState viscosity
    (wholeFiniteSupportActionModes modes)
    (wholeFiniteSupportAffineActionState viscosity step modes state)

/-- The generated next action is exactly the quadratic action-tube
polynomial on every whole Fourier row. -/
theorem wholeFiniteSupportAffineNextActionState_apply_eq_actionTube
    (viscosity step : Real)
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave : IntegerWavevector,
      wave ∉ modes → state wave = 0)
    (stateTransverse : WholeStateTransverse state)
    (output : IntegerWavevector) :
    let action := wholeFiniteSupportActionState viscosity modes state
    wholeFiniteSupportAffineNextActionState viscosity step modes state output =
      action output +
        step • wholeGeneratorLinearizationRow viscosity state action output +
        step ^ 2 • wholeGeneratorQuadraticRow action output := by
  dsimp only [wholeFiniteSupportAffineNextActionState]
  rw [wholeFiniteSupportActionState_apply_eq_wholeTangent
    viscosity (wholeFiniteSupportActionModes modes)
    (wholeFiniteSupportAffineActionState viscosity step modes state)
    (wholeFiniteSupportAffineActionState_supported
      viscosity step modes state supported) output]
  exact wholeLatticeVorticityFourierTangentAt_affine_exactActionTube
    viscosity step modes state supported stateTransverse output

end
end ThreeDimensionalVorticityCoefficientFiniteSupportWholeActionTube
end NavierStokes
end SaturationMonoid
