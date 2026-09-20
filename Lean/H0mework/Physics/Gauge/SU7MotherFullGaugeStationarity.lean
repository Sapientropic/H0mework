import H0mework.Physics.Gauge.SU7MotherGaugeActionVariations
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Full SU(7)-direction stationarity of the mother action

The Stage-5 stationary lift is tested here against every matrix direction in
the real `su(7)` Lie carrier, including directions transverse to the selected
P286 block image.  A norm-coherent variation wrapper is linearly equivalent
to the entire `SU7MotherLieMatrix`; it does not restrict variations to the
three sector readouts.

For the connection potential, exterior derivative, auxiliary two-form, and
constitutive multiplier, the actual Fréchet derivative of the same mother
action is zero at the source lift.  The off-block penalty supplies a genuine
quadratic response whose derivative vanishes at the selected block point but
whose positive regression away from that point remains in the action.
-/

namespace SaturationMonoid.PhysicsCore.SU7MotherFullGaugeStationarity

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7MotherGaugeAction
open EmpiricalReferenceScaleCouplingBoundary
open UnifiedPhysicalMasterAction
open SourceRelativePhysicalStationaryFamily
open NonseparableGravityGaugeSourceAction
open NonseparableMasterActionVariations
open NonzeroSourceGaugeStationaryConfiguration
open PhysicalIIPlusFrechetVariation
open JetLocalPhysicalPlebanskiAction
open SourceGeneratedPhysicalPlebanskiConfiguration
open scoped Matrix.Norms.Elementwise

noncomputable section

@[ext] theorem gaugeSectorConfiguration_ext
    {first second : GaugeSectorConfiguration}
    (curvature : first.curvature = second.curvature)
    (auxiliary : first.auxiliary = second.auxiliary)
    (multiplier : first.constitutiveMultiplier =
      second.constitutiveMultiplier) :
    first = second := by
  cases first
  cases second
  simp_all

/-- A norm-coherent copy of the full SU(7) Lie carrier.  This wrapper avoids
the independently generated topology and additive instances on a submodule
subtype while retaining every SU(7) direction exactly. -/
@[ext] structure MotherLieVariation where
  toLie : SU7MotherLieMatrix

private def motherLieVariationEquiv :
    MotherLieVariation ≃ SU7MotherLieMatrix where
  toFun := MotherLieVariation.toLie
  invFun := MotherLieVariation.mk
  left_inv := by intro value; cases value; rfl
  right_inv := by intro value; rfl

noncomputable instance motherLieVariationNormedAddCommGroup :
    NormedAddCommGroup MotherLieVariation :=
  motherLieVariationEquiv.normedAddCommGroup

noncomputable instance motherLieVariationNormedSpace :
    NormedSpace ℝ MotherLieVariation :=
  motherLieVariationEquiv.normedSpace ℝ

def motherLieVariationToAmbientLinearMap :
    MotherLieVariation →ₗ[ℝ]
      Matrix SU7MotherIndex SU7MotherIndex ℂ where
  toFun := fun value => value.toLie
  map_add' := by intro first second; rfl
  map_smul' := by intro scalar value; rfl

noncomputable instance motherLieVariationFiniteDimensional :
    FiniteDimensional ℝ MotherLieVariation :=
  FiniteDimensional.of_injective motherLieVariationToAmbientLinearMap
    (fun _ _ equality => MotherLieVariation.ext (Subtype.ext equality))

def motherLieVariationToAmbientCLM :
    MotherLieVariation →L[ℝ]
      Matrix SU7MotherIndex SU7MotherIndex ℂ :=
  motherLieVariationToAmbientLinearMap.mkContinuous 1 (by
    intro value
    change ‖(value.toLie : Matrix SU7MotherIndex SU7MotherIndex ℂ)‖ ≤
      1 * ‖(value.toLie : Matrix SU7MotherIndex SU7MotherIndex ℂ)‖
    simp)

def MotherLieVariation.ofLie
    (matrix : SU7MotherLieMatrix) : MotherLieVariation :=
  ⟨matrix⟩

@[simp] theorem MotherLieVariation.toLie_ofLie
    (matrix : SU7MotherLieMatrix) :
    (MotherLieVariation.ofLie matrix).toLie = matrix :=
  rfl

@[simp] theorem MotherLieVariation.ofLie_toLie
    (variation : MotherLieVariation) :
    MotherLieVariation.ofLie variation.toLie = variation := by
  cases variation
  rfl

@[simp] theorem MotherLieVariation.toLie_zero :
    (0 : MotherLieVariation).toLie = 0 :=
  rfl

@[simp] theorem MotherLieVariation.toLie_add
    (first second : MotherLieVariation) :
    (first + second).toLie = first.toLie + second.toLie :=
  rfl

@[simp] theorem MotherLieVariation.toLie_smul
    (scalar : ℝ) (variation : MotherLieVariation) :
    (scalar • variation).toLie = scalar • variation.toLie :=
  rfl

def motherVariationEntryCLM (row column : SU7MotherIndex) :
    MotherLieVariation →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj column).comp
    ((ContinuousLinearMap.proj row).comp
      motherLieVariationToAmbientCLM)

@[simp] theorem motherVariationEntryCLM_apply
    (row column : SU7MotherIndex) (matrix : MotherLieVariation) :
    motherVariationEntryCLM row column matrix =
      (matrix.toLie : Matrix SU7MotherIndex SU7MotherIndex ℂ) row column := by
  change motherLieVariationToAmbientLinearMap matrix row column = _
  rfl

def motherVariationEntryGaugeLinearMap
    (row column : SU7MotherIndex) :
    MotherLieVariation →ₗ[ℝ] DynamicGaugeVector where
  toFun := fun matrix index =>
    if index = 0 then
      ((matrix.toLie : Matrix SU7MotherIndex SU7MotherIndex ℂ)
        row column).re
    else if index = 1 then
      ((matrix.toLie : Matrix SU7MotherIndex SU7MotherIndex ℂ)
        row column).im
    else 0
  map_add' := by
    intro first second
    funext index
    by_cases indexZero : index = 0
    · simp [indexZero]
    · by_cases indexOne : index = 1
      · simp [indexOne]
      · simp [indexZero, indexOne]
  map_smul' := by
    intro scalar matrix
    funext index
    by_cases indexZero : index = 0
    · simp [indexZero]
    · by_cases indexOne : index = 1
      · simp [indexOne]
      · simp [indexZero, indexOne]

def motherVariationEntryGaugeCLM
    (row column : SU7MotherIndex) :
    MotherLieVariation →L[ℝ] DynamicGaugeVector where
  toLinearMap := motherVariationEntryGaugeLinearMap row column
  cont := (motherVariationEntryGaugeLinearMap row column)
    |>.continuous_of_finiteDimensional

@[simp] theorem gaugePairing_motherVariationEntryGaugeCLM
    (row column : SU7MotherIndex) (matrix : MotherLieVariation) :
    gaugePairing
        (motherVariationEntryGaugeCLM row column matrix)
        (motherVariationEntryGaugeCLM row column matrix) =
      Complex.normSq
        ((matrix.toLie : Matrix SU7MotherIndex SU7MotherIndex ℂ)
          row column) := by
  simp [gaugePairing, motherVariationEntryGaugeCLM,
    motherVariationEntryGaugeLinearMap, Complex.normSq,
    Fin.sum_univ_succ]

theorem normSq_entry_hasFDerivAt_zero_of_entry_zero
    (matrix : MotherLieVariation) (row column : SU7MotherIndex)
    (entryZero :
      (matrix.toLie : Matrix SU7MotherIndex SU7MotherIndex ℂ) row column = 0) :
    HasFDerivAt
      (fun candidate : MotherLieVariation =>
        Complex.normSq
          ((candidate.toLie : Matrix SU7MotherIndex SU7MotherIndex ℂ)
            row column))
      (0 : MotherLieVariation →L[ℝ] ℝ) matrix := by
  let entryMap : MotherLieVariation →L[ℝ] DynamicGaugeVector :=
    motherVariationEntryGaugeCLM row column
  have entryMapAt : entryMap matrix = 0 := by
    funext index
    fin_cases index <;>
      simp [entryMap, motherVariationEntryGaugeCLM,
        motherVariationEntryGaugeLinearMap, entryZero]
  have outerDerivative :
      HasFDerivAt
        (fun value : DynamicGaugeVector => gaugePairing value value)
        (0 : GaugeCovector) (entryMap matrix) := by
    simpa only [entryMapAt] using gaugePairing_self_hasFDerivAt_zero
  have composed := outerDerivative.comp matrix entryMap.hasFDerivAt
  have composedZero :
      HasFDerivAt
        ((fun value : DynamicGaugeVector => gaugePairing value value) ∘
          entryMap)
        (0 : MotherLieVariation →L[ℝ] ℝ) matrix :=
    composed.congr_fderiv (by simp)
  apply composedZero.congr_of_eventuallyEq
  filter_upwards [] with candidate
  exact (gaugePairing_motherVariationEntryGaugeCLM
    row column candidate).symm

theorem offBlockEnergy_toLie_hasFDerivAt_zero
    (matrix : MotherLieVariation)
    (crossEntriesZero : ∀ row column,
      breakingLevel row ≠ breakingLevel column →
        (matrix.toLie : Matrix SU7MotherIndex SU7MotherIndex ℂ)
          row column = 0) :
    HasFDerivAt (fun candidate : MotherLieVariation =>
        offBlockEnergy candidate.toLie)
      (0 : MotherLieVariation →L[ℝ] ℝ) matrix := by
  unfold offBlockEnergy
  have innerDerivative (row : SU7MotherIndex) :
      HasFDerivAt
        (fun candidate : MotherLieVariation =>
          ∑ column : SU7MotherIndex,
            if breakingLevel row = breakingLevel column then 0
            else Complex.normSq
              ((candidate.toLie :
                Matrix SU7MotherIndex SU7MotherIndex ℂ) row column))
        (0 : MotherLieVariation →L[ℝ] ℝ) matrix := by
    simpa only [Finset.sum_const_zero] using
      (HasFDerivAt.fun_sum (u := Finset.univ) (x := matrix)
        (A' := fun _ => (0 : MotherLieVariation →L[ℝ] ℝ))
        (fun column _ => by
          by_cases sameLevel : breakingLevel row = breakingLevel column
          · simpa [sameLevel] using
              (hasFDerivAt_const (𝕜 := ℝ) (x := matrix) (c := (0 : ℝ)))
          · simpa [sameLevel] using
              normSq_entry_hasFDerivAt_zero_of_entry_zero
                matrix row column (crossEntriesZero row column sameLevel)))
  simpa only [Finset.sum_const_zero] using
    (HasFDerivAt.fun_sum (u := Finset.univ) (x := matrix)
      (A' := fun _ => (0 : MotherLieVariation →L[ℝ] ℝ))
      (fun row _ => innerDerivative row))

abbrev MotherPotentialVariation :=
  LorentzianIndex → MotherLieVariation

abbrev MotherTwoFormVariation :=
  Fin 6 → MotherLieVariation

def motherPotentialVariationOf
    (potential : LorentzianIndex → SU7MotherLieMatrix) :
    MotherPotentialVariation :=
  fun direction => MotherLieVariation.ofLie (potential direction)

def motherTwoFormVariationOf
    (field : Fin 6 → SU7MotherLieMatrix) :
    MotherTwoFormVariation :=
  fun pair => MotherLieVariation.ofLie (field pair)

def replaceMotherPotential
    (q : SU7MotherUnifiedConfiguration)
    (potential : MotherPotentialVariation) :
    SU7MotherUnifiedConfiguration :=
  { q with
    gauge := { q.gauge with
      connection := { q.gauge.connection with
        potential := fun direction => (potential direction).toLie } } }

def replaceMotherExteriorDerivative
    (q : SU7MotherUnifiedConfiguration)
    (exteriorDerivative : MotherTwoFormVariation) :
    SU7MotherUnifiedConfiguration :=
  { q with
    gauge := { q.gauge with
      connection := { q.gauge.connection with
        exteriorDerivative := fun pair =>
          (exteriorDerivative pair).toLie } } }

def replaceMotherAuxiliary
    (q : SU7MotherUnifiedConfiguration)
    (auxiliary : MotherTwoFormVariation) :
    SU7MotherUnifiedConfiguration :=
  { q with
    gauge := { q.gauge with
      auxiliary := fun pair => (auxiliary pair).toLie } }

def replaceMotherMultiplier
    (q : SU7MotherUnifiedConfiguration)
    (multiplier : MotherTwoFormVariation) :
    SU7MotherUnifiedConfiguration :=
  { q with
    gauge := { q.gauge with
      constitutiveMultiplier := fun pair => (multiplier pair).toLie } }

theorem summedOffBlockEnergy_hasFDerivAt_zero
    {index : Type*} [Fintype index] [DecidableEq index]
    (field : index → MotherLieVariation)
    (crossEntriesZero : ∀ coordinate row column,
      breakingLevel row ≠ breakingLevel column →
        ((field coordinate).toLie :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) row column = 0) :
    HasFDerivAt
      (fun candidate : index → MotherLieVariation =>
        ∑ coordinate : index, offBlockEnergy (candidate coordinate).toLie)
      (0 : (index → MotherLieVariation) →L[ℝ] ℝ) field := by
  have coordinateDerivative (coordinate : index) :
      HasFDerivAt
        (fun candidate : index → MotherLieVariation =>
          offBlockEnergy (candidate coordinate).toLie)
        (0 : (index → MotherLieVariation) →L[ℝ] ℝ) field := by
    have outerDerivative := offBlockEnergy_toLie_hasFDerivAt_zero
      (field coordinate) (crossEntriesZero coordinate)
    have composed := outerDerivative.comp field
      (ContinuousLinearMap.proj coordinate :
        (index → MotherLieVariation) →L[ℝ] MotherLieVariation).hasFDerivAt
    have composedZero :
        HasFDerivAt
          ((fun matrix : MotherLieVariation =>
              offBlockEnergy matrix.toLie) ∘
            (ContinuousLinearMap.proj coordinate :
              (index → MotherLieVariation) →L[ℝ] MotherLieVariation))
          (0 : (index → MotherLieVariation) →L[ℝ] ℝ) field :=
      composed.congr_fderiv (by simp)
    apply composedZero.congr_of_eventuallyEq
    filter_upwards [] with candidate
    rfl
  simpa only [Finset.sum_const_zero] using
    (HasFDerivAt.fun_sum (u := Finset.univ) (x := field)
      (A' := fun _ =>
        (0 : (index → MotherLieVariation) →L[ℝ] ℝ))
      (fun coordinate _ => coordinateDerivative coordinate))

theorem liftSectorValue_crossEntries_zero
    (source : Source) (strong weak hypercharge : ℝ)
    (row column : SU7MotherIndex)
    (differentLevel : breakingLevel row ≠ breakingLevel column) :
    ((liftSectorValue strong weak hypercharge : SU7MotherLieMatrix) :
      Matrix SU7MotherIndex SU7MotherIndex ℂ) row column = 0 := by
  apply selected_entry_zero_of_breakingLevel_ne source
    (liftSectorValue strong weak hypercharge) ?_
    row column differentLevel
  change SelectedBySourceBreaking source
    (p286LieBlockEmbed (sectorP286Value strong weak hypercharge))
  exact p286LieBlockEmbed_selected source _

theorem liftStageFive_potential_crossEntries_zero
    (q : UnifiedConfiguration) (direction : LorentzianIndex)
    (row column : SU7MotherIndex)
    (_differentLevel : breakingLevel row ≠ breakingLevel column) :
    (((motherPotentialVariationOf
        (liftStageFiveUnifiedConfiguration q).gauge.connection.potential)
      direction).toLie : Matrix SU7MotherIndex SU7MotherIndex ℂ)
      row column = 0 := by
  simp [motherPotentialVariationOf, liftStageFiveUnifiedConfiguration,
    liftStageFiveGaugeConfiguration]

theorem liftStageFive_exterior_crossEntries_zero
    (source : Source) (q : UnifiedConfiguration) (pair : Fin 6)
    (row column : SU7MotherIndex)
    (differentLevel : breakingLevel row ≠ breakingLevel column) :
    (((motherTwoFormVariationOf
        (liftStageFiveUnifiedConfiguration q).gauge.connection.exteriorDerivative)
      pair).toLie : Matrix SU7MotherIndex SU7MotherIndex ℂ)
      row column = 0 := by
  exact liftSectorValue_crossEntries_zero source _ _ _
    row column differentLevel

theorem liftStageFive_auxiliary_crossEntries_zero
    (source : Source) (q : UnifiedConfiguration) (pair : Fin 6)
    (row column : SU7MotherIndex)
    (differentLevel : breakingLevel row ≠ breakingLevel column) :
    (((motherTwoFormVariationOf
        (liftStageFiveUnifiedConfiguration q).gauge.auxiliary)
      pair).toLie : Matrix SU7MotherIndex SU7MotherIndex ℂ)
      row column = 0 := by
  exact liftSectorValue_crossEntries_zero source _ _ _
    row column differentLevel

theorem liftStageFive_multiplier_crossEntries_zero
    (source : Source) (q : UnifiedConfiguration) (pair : Fin 6)
    (row column : SU7MotherIndex)
    (differentLevel : breakingLevel row ≠ breakingLevel column) :
    (((motherTwoFormVariationOf
        (liftStageFiveUnifiedConfiguration q).gauge.constitutiveMultiplier)
      pair).toLie : Matrix SU7MotherIndex SU7MotherIndex ℂ)
      row column = 0 := by
  exact liftSectorValue_crossEntries_zero source _ _ _
    row column differentLevel

def motherColorTwoFormLinearMap :
    MotherTwoFormVariation →ₗ[ℝ] DynamicGaugeVector where
  toFun := fun field pair => motherColorCoordinate (field pair).toLie
  map_add' := by
    intro first second
    funext pair
    simp [motherColorCoordinate]
  map_smul' := by
    intro scalar field
    funext pair
    simp [motherColorCoordinate]

def motherWeakTwoFormLinearMap :
    MotherTwoFormVariation →ₗ[ℝ] DynamicGaugeVector where
  toFun := fun field pair => motherWeakCoordinate (field pair).toLie
  map_add' := by
    intro first second
    funext pair
    simp [motherWeakCoordinate]
  map_smul' := by
    intro scalar field
    funext pair
    simp [motherWeakCoordinate]

def motherHyperchargeTwoFormLinearMap :
    MotherTwoFormVariation →ₗ[ℝ] DynamicGaugeVector where
  toFun := fun field pair =>
    motherHyperchargeCoordinate (field pair).toLie
  map_add' := by
    intro first second
    funext pair
    simp [motherHyperchargeCoordinate]
  map_smul' := by
    intro scalar field
    funext pair
    simp [motherHyperchargeCoordinate]

def motherColorTwoFormCLM :
    MotherTwoFormVariation →L[ℝ] DynamicGaugeVector where
  toLinearMap := motherColorTwoFormLinearMap
  cont := motherColorTwoFormLinearMap.continuous_of_finiteDimensional

def motherWeakTwoFormCLM :
    MotherTwoFormVariation →L[ℝ] DynamicGaugeVector where
  toLinearMap := motherWeakTwoFormLinearMap
  cont := motherWeakTwoFormLinearMap.continuous_of_finiteDimensional

def motherHyperchargeTwoFormCLM :
    MotherTwoFormVariation →L[ℝ] DynamicGaugeVector where
  toLinearMap := motherHyperchargeTwoFormLinearMap
  cont := motherHyperchargeTwoFormLinearMap.continuous_of_finiteDimensional

@[simp] theorem motherColorTwoFormCLM_apply
    (field : MotherTwoFormVariation) (pair : Fin 6) :
    motherColorTwoFormCLM field pair =
      motherColorCoordinate (field pair).toLie :=
  rfl

@[simp] theorem motherWeakTwoFormCLM_apply
    (field : MotherTwoFormVariation) (pair : Fin 6) :
    motherWeakTwoFormCLM field pair =
      motherWeakCoordinate (field pair).toLie :=
  rfl

@[simp] theorem motherHyperchargeTwoFormCLM_apply
    (field : MotherTwoFormVariation) (pair : Fin 6) :
    motherHyperchargeTwoFormCLM field pair =
      motherHyperchargeCoordinate (field pair).toLie :=
  rfl

theorem motherAuxiliaryReadouts_at_sourceLift
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    let q := sourceMotherLiftedConfiguration source boundary
    let auxiliary := motherTwoFormVariationOf q.gauge.auxiliary
    motherColorTwoFormCLM auxiliary =
        sourceGaugeAuxiliary source boundary.strongCouplingSquared ∧
      motherWeakTwoFormCLM auxiliary =
        sourceGaugeAuxiliary source boundary.weakCouplingSquared ∧
      motherHyperchargeTwoFormCLM auxiliary =
        sourceGaugeAuxiliary source boundary.hyperchargeCouplingSquared := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩ <;> funext pair <;>
    simp [motherTwoFormVariationOf, sourceMotherLiftedConfiguration,
      liftStageFiveUnifiedConfiguration, liftStageFiveGaugeConfiguration,
      sourceNonseparableConfiguration, sourceStandardModelGaugeConfiguration,
      sourceGaugeSectorConfiguration]

def replaceMotherConnection
    (q : SU7MotherUnifiedConfiguration)
    (connection : SU7MotherGaugeConnection) :
    SU7MotherUnifiedConfiguration :=
  { q with gauge := { q.gauge with connection := connection } }

theorem sourceLifted_connection_gaugeAction_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (connection : SU7MotherGaugeConnection) :
    let q := sourceMotherLiftedConfiguration source boundary
    dynamicStandardModelGaugeAction source q.gravity.tetrad boundary
      (projectMotherGaugeConfiguration
        (replaceMotherConnection q connection).gauge) = 0 := by
  dsimp only
  let q := sourceMotherLiftedConfiguration source boundary
  have strongSector :
      (projectMotherGaugeConfiguration
          (replaceMotherConnection q connection).gauge).strong =
        withGaugeCurvature
          (sourceGaugeSectorConfiguration source
            boundary.strongCouplingSquared)
          (fun pair => motherColorCoordinate
            (motherCurvature connection pair)) := by
    ext pair <;>
      simp [q, replaceMotherConnection,
        sourceMotherLiftedConfiguration, liftStageFiveUnifiedConfiguration,
        liftStageFiveGaugeConfiguration, sourceNonseparableConfiguration,
        sourceStandardModelGaugeConfiguration,
        sourceGaugeSectorConfiguration, projectMotherGaugeConfiguration,
        withGaugeCurvature]
  have weakSector :
      (projectMotherGaugeConfiguration
          (replaceMotherConnection q connection).gauge).weak =
        withGaugeCurvature
          (sourceGaugeSectorConfiguration source
            boundary.weakCouplingSquared)
          (fun pair => motherWeakCoordinate
            (motherCurvature connection pair)) := by
    ext pair <;>
      simp [q, replaceMotherConnection,
        sourceMotherLiftedConfiguration, liftStageFiveUnifiedConfiguration,
        liftStageFiveGaugeConfiguration, sourceNonseparableConfiguration,
        sourceStandardModelGaugeConfiguration,
        sourceGaugeSectorConfiguration, projectMotherGaugeConfiguration,
        withGaugeCurvature]
  have hyperchargeSector :
      (projectMotherGaugeConfiguration
          (replaceMotherConnection q connection).gauge).hypercharge =
        withGaugeCurvature
          (sourceGaugeSectorConfiguration source
            boundary.hyperchargeCouplingSquared)
          (fun pair => motherHyperchargeCoordinate
            (motherCurvature connection pair)) := by
    ext pair <;>
      simp [q, replaceMotherConnection,
        sourceMotherLiftedConfiguration, liftStageFiveUnifiedConfiguration,
        liftStageFiveGaugeConfiguration, sourceNonseparableConfiguration,
        sourceStandardModelGaugeConfiguration,
        sourceGaugeSectorConfiguration, projectMotherGaugeConfiguration,
        withGaugeCurvature]
  rw [dynamicStandardModelGaugeAction, strongSector, weakSector,
    hyperchargeSector]
  rw [show (sourceMotherLiftedConfiguration source boundary).gravity.tetrad =
    tetradVectorAtOrigin source by rfl]
  rw [
    sourceGaugeSector_action_withCurvature_eq_zero,
    sourceGaugeSector_action_withCurvature_eq_zero,
    sourceGaugeSector_action_withCurvature_eq_zero]
  norm_num

theorem sourceLifted_potential_gaugeAction_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (potential : MotherPotentialVariation) :
    let q := sourceMotherLiftedConfiguration source boundary
    dynamicStandardModelGaugeAction source q.gravity.tetrad boundary
      (projectMotherGaugeConfiguration
        (replaceMotherPotential q potential).gauge) = 0 := by
  dsimp only
  simpa [replaceMotherPotential, replaceMotherConnection] using
    sourceLifted_connection_gaugeAction_zero source boundary
      ({ (sourceMotherLiftedConfiguration source boundary).gauge.connection with
        potential := fun direction => (potential direction).toLie } :
        SU7MotherGaugeConnection)

theorem sourceLifted_exterior_gaugeAction_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (exteriorDerivative : MotherTwoFormVariation) :
    let q := sourceMotherLiftedConfiguration source boundary
    dynamicStandardModelGaugeAction source q.gravity.tetrad boundary
      (projectMotherGaugeConfiguration
        (replaceMotherExteriorDerivative q exteriorDerivative).gauge) = 0 := by
  dsimp only
  simpa [replaceMotherExteriorDerivative, replaceMotherConnection] using
    sourceLifted_connection_gaugeAction_zero source boundary
      ({ (sourceMotherLiftedConfiguration source boundary).gauge.connection with
        exteriorDerivative := fun pair => (exteriorDerivative pair).toLie } :
        SU7MotherGaugeConnection)

theorem sourceLifted_multiplier_gaugeAction_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (multiplier : MotherTwoFormVariation) :
    let q := sourceMotherLiftedConfiguration source boundary
    dynamicStandardModelGaugeAction source q.gravity.tetrad boundary
      (projectMotherGaugeConfiguration
        (replaceMotherMultiplier q multiplier).gauge) = 0 := by
  dsimp only
  let q := sourceMotherLiftedConfiguration source boundary
  have strongSector :
      (projectMotherGaugeConfiguration
          (replaceMotherMultiplier q multiplier).gauge).strong =
        (sourceGaugeSectorConfiguration source
          boundary.strongCouplingSquared).withConstitutiveMultiplier
            (motherColorTwoFormCLM multiplier) := by
    ext pair <;>
      simp [q, replaceMotherMultiplier,
        sourceMotherLiftedConfiguration, liftStageFiveUnifiedConfiguration,
        liftStageFiveGaugeConfiguration, sourceNonseparableConfiguration,
        sourceStandardModelGaugeConfiguration,
        sourceGaugeSectorConfiguration, projectMotherGaugeConfiguration,
        GaugeSectorConfiguration.withConstitutiveMultiplier]
  have weakSector :
      (projectMotherGaugeConfiguration
          (replaceMotherMultiplier q multiplier).gauge).weak =
        (sourceGaugeSectorConfiguration source
          boundary.weakCouplingSquared).withConstitutiveMultiplier
            (motherWeakTwoFormCLM multiplier) := by
    ext pair <;>
      simp [q, replaceMotherMultiplier,
        sourceMotherLiftedConfiguration, liftStageFiveUnifiedConfiguration,
        liftStageFiveGaugeConfiguration, sourceNonseparableConfiguration,
        sourceStandardModelGaugeConfiguration,
        sourceGaugeSectorConfiguration, projectMotherGaugeConfiguration,
        GaugeSectorConfiguration.withConstitutiveMultiplier]
  have hyperchargeSector :
      (projectMotherGaugeConfiguration
          (replaceMotherMultiplier q multiplier).gauge).hypercharge =
        (sourceGaugeSectorConfiguration source
          boundary.hyperchargeCouplingSquared).withConstitutiveMultiplier
            (motherHyperchargeTwoFormCLM multiplier) := by
    ext pair <;>
      simp [q, replaceMotherMultiplier,
        sourceMotherLiftedConfiguration, liftStageFiveUnifiedConfiguration,
        liftStageFiveGaugeConfiguration, sourceNonseparableConfiguration,
        sourceStandardModelGaugeConfiguration,
        sourceGaugeSectorConfiguration, projectMotherGaugeConfiguration,
        GaugeSectorConfiguration.withConstitutiveMultiplier]
  rw [dynamicStandardModelGaugeAction, strongSector, weakSector,
    hyperchargeSector]
  rw [show (sourceMotherLiftedConfiguration source boundary).gravity.tetrad =
    tetradVectorAtOrigin source by rfl]
  rw [sourceGaugeSector_action_withMultiplier_eq_zero,
    sourceGaugeSector_action_withMultiplier_eq_zero,
    sourceGaugeSector_action_withMultiplier_eq_zero]
  norm_num

theorem sourceLifted_auxiliary_strongSector
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (auxiliary : MotherTwoFormVariation) :
    let q := sourceMotherLiftedConfiguration source boundary
    (projectMotherGaugeConfiguration
        (replaceMotherAuxiliary q auxiliary).gauge).strong =
      withGaugeAuxiliary
        (sourceGaugeSectorConfiguration source
          boundary.strongCouplingSquared)
        (motherColorTwoFormCLM auxiliary) := by
  dsimp only
  ext pair <;>
    simp [replaceMotherAuxiliary, sourceMotherLiftedConfiguration,
      liftStageFiveUnifiedConfiguration, liftStageFiveGaugeConfiguration,
      sourceNonseparableConfiguration, sourceStandardModelGaugeConfiguration,
      sourceGaugeSectorConfiguration, projectMotherGaugeConfiguration,
      withGaugeAuxiliary]

theorem sourceLifted_auxiliary_weakSector
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (auxiliary : MotherTwoFormVariation) :
    let q := sourceMotherLiftedConfiguration source boundary
    (projectMotherGaugeConfiguration
        (replaceMotherAuxiliary q auxiliary).gauge).weak =
      withGaugeAuxiliary
        (sourceGaugeSectorConfiguration source
          boundary.weakCouplingSquared)
        (motherWeakTwoFormCLM auxiliary) := by
  dsimp only
  ext pair <;>
    simp [replaceMotherAuxiliary, sourceMotherLiftedConfiguration,
      liftStageFiveUnifiedConfiguration, liftStageFiveGaugeConfiguration,
      sourceNonseparableConfiguration, sourceStandardModelGaugeConfiguration,
      sourceGaugeSectorConfiguration, projectMotherGaugeConfiguration,
      withGaugeAuxiliary]

theorem sourceLifted_auxiliary_hyperchargeSector
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings)
    (auxiliary : MotherTwoFormVariation) :
    let q := sourceMotherLiftedConfiguration source boundary
    (projectMotherGaugeConfiguration
        (replaceMotherAuxiliary q auxiliary).gauge).hypercharge =
      withGaugeAuxiliary
        (sourceGaugeSectorConfiguration source
          boundary.hyperchargeCouplingSquared)
        (motherHyperchargeTwoFormCLM auxiliary) := by
  dsimp only
  ext pair <;>
    simp [replaceMotherAuxiliary, sourceMotherLiftedConfiguration,
      liftStageFiveUnifiedConfiguration, liftStageFiveGaugeConfiguration,
      sourceNonseparableConfiguration, sourceStandardModelGaugeConfiguration,
      sourceGaugeSectorConfiguration, projectMotherGaugeConfiguration,
      withGaugeAuxiliary]

theorem sourceLifted_auxiliary_gaugeAction_hasFDerivAt_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    let q := sourceMotherLiftedConfiguration source boundary
    let base := motherTwoFormVariationOf q.gauge.auxiliary
    HasFDerivAt
      (fun auxiliary : MotherTwoFormVariation =>
        dynamicStandardModelGaugeAction source q.gravity.tetrad boundary
          (projectMotherGaugeConfiguration
            (replaceMotherAuxiliary q auxiliary).gauge))
      (0 : MotherTwoFormVariation →L[ℝ] ℝ) base := by
  dsimp only
  let q := sourceMotherLiftedConfiguration source boundary
  let base := motherTwoFormVariationOf q.gauge.auxiliary
  have readouts := motherAuxiliaryReadouts_at_sourceLift source boundary
  have strongOuter :
      HasFDerivAt
        (fun auxiliary : DynamicGaugeVector =>
          dynamicGaugeSectorAction source (tetradVectorAtOrigin source)
            boundary.strongCouplingSquared
            (withGaugeAuxiliary
              (sourceGaugeSectorConfiguration source
                boundary.strongCouplingSquared) auxiliary))
        (0 : GaugeCovector) (motherColorTwoFormCLM base) := by
    rw [readouts.1]
    exact (actual_dynamicGauge_auxiliary_derivative source
      (tetradVectorAtOrigin source) boundary.strongCouplingSquared
      (sourceGaugeSectorConfiguration source
        boundary.strongCouplingSquared)).congr_fderiv
      (sourceGaugeSector_deltaAuxiliary_zero source
        boundary.strongCouplingSquared)
  have weakOuter :
      HasFDerivAt
        (fun auxiliary : DynamicGaugeVector =>
          dynamicGaugeSectorAction source (tetradVectorAtOrigin source)
            boundary.weakCouplingSquared
            (withGaugeAuxiliary
              (sourceGaugeSectorConfiguration source
                boundary.weakCouplingSquared) auxiliary))
        (0 : GaugeCovector) (motherWeakTwoFormCLM base) := by
    rw [readouts.2.1]
    exact (actual_dynamicGauge_auxiliary_derivative source
      (tetradVectorAtOrigin source) boundary.weakCouplingSquared
      (sourceGaugeSectorConfiguration source
        boundary.weakCouplingSquared)).congr_fderiv
      (sourceGaugeSector_deltaAuxiliary_zero source
        boundary.weakCouplingSquared)
  have hyperchargeOuter :
      HasFDerivAt
        (fun auxiliary : DynamicGaugeVector =>
          dynamicGaugeSectorAction source (tetradVectorAtOrigin source)
            boundary.hyperchargeCouplingSquared
            (withGaugeAuxiliary
              (sourceGaugeSectorConfiguration source
                boundary.hyperchargeCouplingSquared) auxiliary))
        (0 : GaugeCovector) (motherHyperchargeTwoFormCLM base) := by
    rw [readouts.2.2]
    exact (actual_dynamicGauge_auxiliary_derivative source
      (tetradVectorAtOrigin source) boundary.hyperchargeCouplingSquared
      (sourceGaugeSectorConfiguration source
        boundary.hyperchargeCouplingSquared)).congr_fderiv
      (sourceGaugeSector_deltaAuxiliary_zero source
        boundary.hyperchargeCouplingSquared)
  have strongComposed := strongOuter.comp base
    motherColorTwoFormCLM.hasFDerivAt
  have weakComposed := weakOuter.comp base
    motherWeakTwoFormCLM.hasFDerivAt
  have hyperchargeComposed := hyperchargeOuter.comp base
    motherHyperchargeTwoFormCLM.hasFDerivAt
  have strongZero :
      HasFDerivAt
        ((fun auxiliary : DynamicGaugeVector =>
          dynamicGaugeSectorAction source (tetradVectorAtOrigin source)
            boundary.strongCouplingSquared
            (withGaugeAuxiliary
              (sourceGaugeSectorConfiguration source
                boundary.strongCouplingSquared) auxiliary)) ∘
          motherColorTwoFormCLM)
        (0 : MotherTwoFormVariation →L[ℝ] ℝ) base :=
    strongComposed.congr_fderiv (by simp)
  have weakZero :
      HasFDerivAt
        ((fun auxiliary : DynamicGaugeVector =>
          dynamicGaugeSectorAction source (tetradVectorAtOrigin source)
            boundary.weakCouplingSquared
            (withGaugeAuxiliary
              (sourceGaugeSectorConfiguration source
                boundary.weakCouplingSquared) auxiliary)) ∘
          motherWeakTwoFormCLM)
        (0 : MotherTwoFormVariation →L[ℝ] ℝ) base :=
    weakComposed.congr_fderiv (by simp)
  have hyperchargeZero :
      HasFDerivAt
        ((fun auxiliary : DynamicGaugeVector =>
          dynamicGaugeSectorAction source (tetradVectorAtOrigin source)
            boundary.hyperchargeCouplingSquared
            (withGaugeAuxiliary
              (sourceGaugeSectorConfiguration source
                boundary.hyperchargeCouplingSquared) auxiliary)) ∘
          motherHyperchargeTwoFormCLM)
        (0 : MotherTwoFormVariation →L[ℝ] ℝ) base :=
    hyperchargeComposed.congr_fderiv (by simp)
  have total := (strongZero.add weakZero).add hyperchargeZero
  have totalZero : HasFDerivAt _
      (0 : MotherTwoFormVariation →L[ℝ] ℝ) base :=
    total.congr_fderiv (by simp)
  apply totalZero.congr_of_eventuallyEq
  filter_upwards [] with auxiliary
  rw [dynamicStandardModelGaugeAction,
    sourceLifted_auxiliary_strongSector source boundary auxiliary,
    sourceLifted_auxiliary_weakSector source boundary auxiliary,
    sourceLifted_auxiliary_hyperchargeSector source boundary auxiliary]
  rfl

theorem sourceLifted_potential_penalty_hasFDerivAt_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    let q := sourceMotherLiftedConfiguration source boundary
    let base := motherPotentialVariationOf q.gauge.connection.potential
    HasFDerivAt
      (fun potential : MotherPotentialVariation =>
        motherBreakingPenalty (replaceMotherPotential q potential).gauge)
      (0 : MotherPotentialVariation →L[ℝ] ℝ) base := by
  dsimp only
  let stageFive := sourceNonseparableConfiguration source boundary
  let q := sourceMotherLiftedConfiguration source boundary
  let base := motherPotentialVariationOf q.gauge.connection.potential
  have variableDerivative := summedOffBlockEnergy_hasFDerivAt_zero base
    (fun direction row column differentLevel => by
      exact liftStageFive_potential_crossEntries_zero stageFive direction
        row column differentLevel)
  let exteriorConstant := ∑ pair : Fin 6,
    offBlockEnergy (q.gauge.connection.exteriorDerivative pair)
  let auxiliaryConstant := ∑ pair : Fin 6,
    offBlockEnergy (q.gauge.auxiliary pair)
  let multiplierConstant := ∑ pair : Fin 6,
    offBlockEnergy (q.gauge.constitutiveMultiplier pair)
  have total := ((variableDerivative.add_const exteriorConstant).add_const
    auxiliaryConstant).add_const multiplierConstant
  apply total.congr_of_eventuallyEq
  filter_upwards [] with potential
  rfl

theorem sourceLifted_exterior_penalty_hasFDerivAt_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    let q := sourceMotherLiftedConfiguration source boundary
    let base := motherTwoFormVariationOf
      q.gauge.connection.exteriorDerivative
    HasFDerivAt
      (fun exteriorDerivative : MotherTwoFormVariation =>
        motherBreakingPenalty
          (replaceMotherExteriorDerivative q exteriorDerivative).gauge)
      (0 : MotherTwoFormVariation →L[ℝ] ℝ) base := by
  dsimp only
  let stageFive := sourceNonseparableConfiguration source boundary
  let q := sourceMotherLiftedConfiguration source boundary
  let base := motherTwoFormVariationOf
    q.gauge.connection.exteriorDerivative
  have variableDerivative := summedOffBlockEnergy_hasFDerivAt_zero base
    (fun pair row column differentLevel => by
      exact liftStageFive_exterior_crossEntries_zero source stageFive pair
        row column differentLevel)
  let potentialConstant := ∑ direction : LorentzianIndex,
    offBlockEnergy (q.gauge.connection.potential direction)
  let auxiliaryConstant := ∑ pair : Fin 6,
    offBlockEnergy (q.gauge.auxiliary pair)
  let multiplierConstant := ∑ pair : Fin 6,
    offBlockEnergy (q.gauge.constitutiveMultiplier pair)
  have total := (((variableDerivative.const_add potentialConstant).add_const
    auxiliaryConstant).add_const multiplierConstant)
  apply total.congr_of_eventuallyEq
  filter_upwards [] with exteriorDerivative
  rfl

theorem sourceLifted_auxiliary_penalty_hasFDerivAt_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    let q := sourceMotherLiftedConfiguration source boundary
    let base := motherTwoFormVariationOf q.gauge.auxiliary
    HasFDerivAt
      (fun auxiliary : MotherTwoFormVariation =>
        motherBreakingPenalty (replaceMotherAuxiliary q auxiliary).gauge)
      (0 : MotherTwoFormVariation →L[ℝ] ℝ) base := by
  dsimp only
  let stageFive := sourceNonseparableConfiguration source boundary
  let q := sourceMotherLiftedConfiguration source boundary
  let base := motherTwoFormVariationOf q.gauge.auxiliary
  have variableDerivative := summedOffBlockEnergy_hasFDerivAt_zero base
    (fun pair row column differentLevel => by
      exact liftStageFive_auxiliary_crossEntries_zero source stageFive pair
        row column differentLevel)
  let connectionConstant :=
    (∑ direction : LorentzianIndex,
        offBlockEnergy (q.gauge.connection.potential direction)) +
      ∑ pair : Fin 6,
        offBlockEnergy (q.gauge.connection.exteriorDerivative pair)
  let multiplierConstant := ∑ pair : Fin 6,
    offBlockEnergy (q.gauge.constitutiveMultiplier pair)
  have total := (variableDerivative.const_add connectionConstant).add_const
    multiplierConstant
  apply total.congr_of_eventuallyEq
  filter_upwards [] with auxiliary
  rfl

theorem sourceLifted_multiplier_penalty_hasFDerivAt_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    let q := sourceMotherLiftedConfiguration source boundary
    let base := motherTwoFormVariationOf q.gauge.constitutiveMultiplier
    HasFDerivAt
      (fun multiplier : MotherTwoFormVariation =>
        motherBreakingPenalty (replaceMotherMultiplier q multiplier).gauge)
      (0 : MotherTwoFormVariation →L[ℝ] ℝ) base := by
  dsimp only
  let stageFive := sourceNonseparableConfiguration source boundary
  let q := sourceMotherLiftedConfiguration source boundary
  let base := motherTwoFormVariationOf q.gauge.constitutiveMultiplier
  have variableDerivative := summedOffBlockEnergy_hasFDerivAt_zero base
    (fun pair row column differentLevel => by
      exact liftStageFive_multiplier_crossEntries_zero source stageFive pair
        row column differentLevel)
  let fixedConstant :=
    ((∑ direction : LorentzianIndex,
        offBlockEnergy (q.gauge.connection.potential direction)) +
      ∑ pair : Fin 6,
        offBlockEnergy (q.gauge.connection.exteriorDerivative pair)) +
      ∑ pair : Fin 6, offBlockEnergy (q.gauge.auxiliary pair)
  have total := variableDerivative.const_add fixedConstant
  apply total.congr_of_eventuallyEq
  filter_upwards [] with multiplier
  rfl

theorem sourceLifted_potential_motherAction_hasFDerivAt_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    let q := sourceMotherLiftedConfiguration source boundary
    let base := motherPotentialVariationOf q.gauge.connection.potential
    HasFDerivAt
      (fun potential : MotherPotentialVariation =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (replaceMotherPotential q potential))
      (0 : MotherPotentialVariation →L[ℝ] ℝ) base := by
  dsimp only
  let q := sourceMotherLiftedConfiguration source boundary
  let base := motherPotentialVariationOf q.gauge.connection.potential
  have gaugeDerivative :
      HasFDerivAt
        (fun potential : MotherPotentialVariation =>
          dynamicStandardModelGaugeAction source q.gravity.tetrad boundary
            (projectMotherGaugeConfiguration
              (replaceMotherPotential q potential).gauge))
        (0 : MotherPotentialVariation →L[ℝ] ℝ) base :=
    (hasFDerivAt_const (𝕜 := ℝ) (x := base) (c := (0 : ℝ)))
      |>.congr_of_eventuallyEq (Filter.Eventually.of_forall
        (sourceLifted_potential_gaugeAction_zero source boundary))
  have penaltyDerivative :=
    sourceLifted_potential_penalty_hasFDerivAt_zero source boundary
  have total := (gaugeDerivative.const_add
    (sourceRelativeMasterAction source q.gravity)).add penaltyDerivative
  have totalZero : HasFDerivAt _
      (0 : MotherPotentialVariation →L[ℝ] ℝ) base :=
    total.congr_fderiv (by simp)
  apply totalZero.congr_of_eventuallyEq
  filter_upwards [] with potential
  simp [motherMasterAction, replaceMotherPotential, q]

theorem sourceLifted_exterior_motherAction_hasFDerivAt_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    let q := sourceMotherLiftedConfiguration source boundary
    let base := motherTwoFormVariationOf
      q.gauge.connection.exteriorDerivative
    HasFDerivAt
      (fun exteriorDerivative : MotherTwoFormVariation =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (replaceMotherExteriorDerivative q exteriorDerivative))
      (0 : MotherTwoFormVariation →L[ℝ] ℝ) base := by
  dsimp only
  let q := sourceMotherLiftedConfiguration source boundary
  let base := motherTwoFormVariationOf
    q.gauge.connection.exteriorDerivative
  have gaugeDerivative :
      HasFDerivAt
        (fun exteriorDerivative : MotherTwoFormVariation =>
          dynamicStandardModelGaugeAction source q.gravity.tetrad boundary
            (projectMotherGaugeConfiguration
              (replaceMotherExteriorDerivative q exteriorDerivative).gauge))
        (0 : MotherTwoFormVariation →L[ℝ] ℝ) base :=
    (hasFDerivAt_const (𝕜 := ℝ) (x := base) (c := (0 : ℝ)))
      |>.congr_of_eventuallyEq (Filter.Eventually.of_forall
        (sourceLifted_exterior_gaugeAction_zero source boundary))
  have penaltyDerivative :=
    sourceLifted_exterior_penalty_hasFDerivAt_zero source boundary
  have total := (gaugeDerivative.const_add
    (sourceRelativeMasterAction source q.gravity)).add penaltyDerivative
  have totalZero : HasFDerivAt _
      (0 : MotherTwoFormVariation →L[ℝ] ℝ) base :=
    total.congr_fderiv (by simp)
  apply totalZero.congr_of_eventuallyEq
  filter_upwards [] with exteriorDerivative
  simp [motherMasterAction, replaceMotherExteriorDerivative, q]

theorem sourceLifted_auxiliary_motherAction_hasFDerivAt_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    let q := sourceMotherLiftedConfiguration source boundary
    let base := motherTwoFormVariationOf q.gauge.auxiliary
    HasFDerivAt
      (fun auxiliary : MotherTwoFormVariation =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (replaceMotherAuxiliary q auxiliary))
      (0 : MotherTwoFormVariation →L[ℝ] ℝ) base := by
  dsimp only
  let q := sourceMotherLiftedConfiguration source boundary
  let base := motherTwoFormVariationOf q.gauge.auxiliary
  have gaugeDerivative :=
    sourceLifted_auxiliary_gaugeAction_hasFDerivAt_zero source boundary
  have penaltyDerivative :=
    sourceLifted_auxiliary_penalty_hasFDerivAt_zero source boundary
  have total := (gaugeDerivative.const_add
    (sourceRelativeMasterAction source q.gravity)).add penaltyDerivative
  have totalZero : HasFDerivAt _
      (0 : MotherTwoFormVariation →L[ℝ] ℝ) base :=
    total.congr_fderiv (by simp)
  apply totalZero.congr_of_eventuallyEq
  filter_upwards [] with auxiliary
  simp [motherMasterAction, replaceMotherAuxiliary, q]

theorem sourceLifted_multiplier_motherAction_hasFDerivAt_zero
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    let q := sourceMotherLiftedConfiguration source boundary
    let base := motherTwoFormVariationOf q.gauge.constitutiveMultiplier
    HasFDerivAt
      (fun multiplier : MotherTwoFormVariation =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (replaceMotherMultiplier q multiplier))
      (0 : MotherTwoFormVariation →L[ℝ] ℝ) base := by
  dsimp only
  let q := sourceMotherLiftedConfiguration source boundary
  let base := motherTwoFormVariationOf q.gauge.constitutiveMultiplier
  have gaugeDerivative :
      HasFDerivAt
        (fun multiplier : MotherTwoFormVariation =>
          dynamicStandardModelGaugeAction source q.gravity.tetrad boundary
            (projectMotherGaugeConfiguration
              (replaceMotherMultiplier q multiplier).gauge))
        (0 : MotherTwoFormVariation →L[ℝ] ℝ) base :=
    (hasFDerivAt_const (𝕜 := ℝ) (x := base) (c := (0 : ℝ)))
      |>.congr_of_eventuallyEq (Filter.Eventually.of_forall
        (sourceLifted_multiplier_gaugeAction_zero source boundary))
  have penaltyDerivative :=
    sourceLifted_multiplier_penalty_hasFDerivAt_zero source boundary
  have total := (gaugeDerivative.const_add
    (sourceRelativeMasterAction source q.gravity)).add penaltyDerivative
  have totalZero : HasFDerivAt _
      (0 : MotherTwoFormVariation →L[ℝ] ℝ) base :=
    total.congr_fderiv (by simp)
  apply totalZero.congr_of_eventuallyEq
  filter_upwards [] with multiplier
  simp [motherMasterAction, replaceMotherMultiplier, q]

/-- Coordinatewise stationarity in every full SU(7) matrix direction of all
four mother-gauge fields.  No off-block direction is omitted. -/
structure FullSU7MotherGaugeStationary
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) : Prop where
  potential :
    let q := sourceMotherLiftedConfiguration source boundary
    HasFDerivAt
      (fun candidate : MotherPotentialVariation =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (replaceMotherPotential q candidate))
      (0 : MotherPotentialVariation →L[ℝ] ℝ)
      (motherPotentialVariationOf q.gauge.connection.potential)
  exteriorDerivative :
    let q := sourceMotherLiftedConfiguration source boundary
    HasFDerivAt
      (fun candidate : MotherTwoFormVariation =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (replaceMotherExteriorDerivative q candidate))
      (0 : MotherTwoFormVariation →L[ℝ] ℝ)
      (motherTwoFormVariationOf q.gauge.connection.exteriorDerivative)
  auxiliary :
    let q := sourceMotherLiftedConfiguration source boundary
    HasFDerivAt
      (fun candidate : MotherTwoFormVariation =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (replaceMotherAuxiliary q candidate))
      (0 : MotherTwoFormVariation →L[ℝ] ℝ)
      (motherTwoFormVariationOf q.gauge.auxiliary)
  multiplier :
    let q := sourceMotherLiftedConfiguration source boundary
    HasFDerivAt
      (fun candidate : MotherTwoFormVariation =>
        motherMasterAction source (motherBoundaryOfStageFive boundary)
          (replaceMotherMultiplier q candidate))
      (0 : MotherTwoFormVariation →L[ℝ] ℝ)
      (motherTwoFormVariationOf q.gauge.constitutiveMultiplier)

theorem source_generates_fullSU7MotherGaugeStationary
    (source : Source) (boundary : EmpiricalReferenceScaleCouplings) :
    FullSU7MotherGaugeStationary source boundary where
  potential := sourceLifted_potential_motherAction_hasFDerivAt_zero
    source boundary
  exteriorDerivative :=
    sourceLifted_exterior_motherAction_hasFDerivAt_zero source boundary
  auxiliary := sourceLifted_auxiliary_motherAction_hasFDerivAt_zero
    source boundary
  multiplier := sourceLifted_multiplier_motherAction_hasFDerivAt_zero
    source boundary

theorem motherLieVariation_covers_every_SU7_direction
    (matrix : SU7MotherLieMatrix) :
    ∃! variation : MotherLieVariation, variation.toLie = matrix := by
  refine ⟨MotherLieVariation.ofLie matrix, rfl, ?_⟩
  intro variation equality
  exact MotherLieVariation.ext (equality.trans rfl)

theorem positiveSource_generates_nonzero_fullSU7MotherGaugeStationary
    (boundary : EmpiricalReferenceScaleCouplings) :
    FullSU7MotherGaugeStationary positiveSource boundary ∧
      (fun pair => motherColorCoordinate
        (motherCurvature
          (sourceMotherLiftedConfiguration
            positiveSource boundary).gauge.connection pair)) ≠ 0 :=
  ⟨source_generates_fullSU7MotherGaugeStationary positiveSource boundary,
    positiveSource_motherLifted_strongCurvature_ne_zero boundary⟩

end
end SaturationMonoid.PhysicsCore.SU7MotherFullGaugeStationarity
