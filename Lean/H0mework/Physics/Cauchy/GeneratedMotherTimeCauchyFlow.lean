import H0mework.Physics.Cauchy.CanonicalCauchyState
import H0mework.Physics.Geometry.FullMotherDescentAndTransport
import H0mework.Physics.MatterJets.SU7ExteriorMatterGaugeCovariantJet
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# S9-C3h89: source-generated non-Abelian mother-time Cauchy flow

The full Stage-8 mother connection already generates an analytic matrix
parallel transport along every coordinate axis.  Its canonical time-axis
generator is the actual source color-Cartan potential.  This module proves
that this particular raw exponential is not merely an invertible matrix:
it is the image of a canonically generated `SU(3)` element and therefore an
actual `SU(7)` element.

The typed transport is then allowed to act, before any residual is inspected:

* on the P286 connection and auxiliary through the actual color adjoint;
* on the breaking scalar and scalar velocity through the existing scalar
  representation;
* on matter and conjugate matter through the existing representation and its
  contragredient action;
* trivially on the Lorentz/gravity fields, as required by an internal color
  action.

The resulting update has zero, composition, inverse, holonomic-restriction,
and Cauchy-flow laws.  Its underlying matrix path is definitionally the
previous source-generated parallel-ODE solution.  Thus the order of
responsibility is

`source connection/path → actual U → actual field action`.

No joint residual, keep, trace, target configuration, shell witness,
stationarity receipt, inverse image, or branch selector occurs in the
construction.  This is a non-Abelian internal transport flow on the complete
primitive carrier, not yet the interacting BF/GR/SM Cauchy development.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSourceGeneratedMotherTimeCauchyFlow

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineStageEightFirstJet
open StageNineFullMotherDescentAndTransport
open StageNineCanonicalCauchyState
open StageNineP286ActionCauchySplit
open StageNineHolonomicField
open StageNineDynamicBreakingVacuum
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorBreakingYukawa
open DiracExteriorMatterAction
open GaugeProjection
open GaugeProjection.ConcreteBlockDiagonal
open Matrix

noncomputable section

set_option autoImplicit false

/-! ## Typed lift of the actual mother time-axis transport -/

/-- The color phase forced by the canonical unit-speed time-axis contraction
of the source mother connection. -/
def sourceMotherTimeColorPhase
    (source : SmoothUnifiedSource) (time : ℝ) : Circle :=
  Circle.exp (-source.legacy.sigma * time)

/-- The corresponding color matrix `diag(z,z⁻¹,1)`. -/
def sourceMotherTimeColorMatrix
    (source : SmoothUnifiedSource) (time : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal fun index =>
    if index = 0 then
      sourceMotherTimeColorPhase source time
    else if index = 1 then
      (sourceMotherTimeColorPhase source time)⁻¹
    else
      1

theorem sourceMotherTimeColorMatrix_mem_specialUnitary
    (source : SmoothUnifiedSource) (time : ℝ) :
    sourceMotherTimeColorMatrix source time ∈
      Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [sourceMotherTimeColorMatrix, Matrix.mul_apply,
        Fin.sum_univ_three]
    all_goals rw [← Circle.coe_inv_eq_conj]
    all_goals simp
  · rw [sourceMotherTimeColorMatrix, Matrix.det_diagonal]
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by
      ext index
      fin_cases index <;> simp]
    simp

/-- The canonical color transport as an actual `SU(3)` element. -/
def sourceMotherTimeColorElement
    (source : SmoothUnifiedSource) (time : ℝ) : SU3Gauge :=
  ⟨sourceMotherTimeColorMatrix source time,
    sourceMotherTimeColorMatrix_mem_specialUnitary source time⟩

/-- The same transport in the actual P286 subgroup. -/
def sourceMotherTimeP286Element
    (source : SmoothUnifiedSource) (time : ℝ) :
    P286ResidualGaugeGroup :=
  (sourceMotherTimeColorElement source time, 1, 1)

/-- Canonical typed `SU(7)` lift of the mother time-axis transport. -/
def sourceGeneratedMotherTimeTransport
    (source : SmoothUnifiedSource) (time : ℝ) : SU7MotherGroup :=
  blockDiagonalSMBlock (sourceMotherTimeP286Element source time)

/-- Diagonal coordinates of the actual canonical time-axis generator. -/
def sourceMotherTimeGeneratorDiagonal
    (source : SmoothUnifiedSource) : SU7MotherIndex → ℂ
  | Sum.inl color =>
      if color = 0 then
        -(source.legacy.sigma : ℂ) * Complex.I
      else if color = 1 then
        (source.legacy.sigma : ℂ) * Complex.I
      else
        0
  | _ => 0

set_option maxHeartbeats 1000000 in
theorem generatedMotherTimeAxisGenerator_eq_diagonal
    (source : SmoothUnifiedSource) :
    generatedMotherAxisGenerator source 0 1 =
      Matrix.diagonal (sourceMotherTimeGeneratorDiagonal source) := by
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [generatedMotherAxisGenerator, stageEightMotherConnection,
      sourceMotherConnection, sourceP286Potential, realScaleP286,
      realScaleHypercharge, p286LieBlockEmbed, rawP286LieBlock,
      weakHyperchargeLieBlock, hyperchargeLieBlock, scalarLieBlock,
      colorCartanGenerator, colorCartanRaw,
      sourceMotherTimeGeneratorDiagonal]

set_option maxHeartbeats 1000000 in
/-- The typed transport is exactly the previously generated raw matrix
exponential, rather than a new parallel-transport ansatz. -/
theorem sourceGeneratedMotherTimeTransport_coe_eq_axisTransport
    (source : SmoothUnifiedSource) (time : ℝ) :
    (sourceGeneratedMotherTimeTransport source time :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) =
      generatedUnifiedMotherAxisTransport source 0 1 time := by
  unfold generatedUnifiedMotherAxisTransport
  rw [generatedMotherTimeAxisGenerator_eq_diagonal,
    ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [sourceGeneratedMotherTimeTransport,
      sourceMotherTimeP286Element, sourceMotherTimeColorElement,
      sourceMotherTimeColorMatrix, sourceMotherTimeColorPhase,
      sourceMotherTimeGeneratorDiagonal, blockDiagonalSMBlock,
      rawBlockDiagonal, weakHyperchargeBlock, hyperchargePairBlock,
      scalarOneBlock, Circle.coe_exp, ← Complex.exp_eq_exp_ℂ]
  · rw [Complex.exp_neg]
    congr 2
    ring
  · congr 1
    ring

open scoped Matrix.Norms.Operator in
/-- The typed path retains the actual parallel ODE generated by the mother
connection. -/
theorem sourceGeneratedMotherTimeTransport_solves_parallelODE
    (source : SmoothUnifiedSource) (time : ℝ) :
    HasDerivAt
      (fun parameter =>
        (sourceGeneratedMotherTimeTransport source parameter :
          Matrix SU7MotherIndex SU7MotherIndex ℂ))
      ((sourceGeneratedMotherTimeTransport source time :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) *
        (-(1 : ℝ)) •
          (generatedUnifiedMotherPotential source
            (generatedMotherAxisPath 0 1 time) 0 :
              Matrix SU7MotherIndex SU7MotherIndex ℂ))
      time := by
  simpa only [
    sourceGeneratedMotherTimeTransport_coe_eq_axisTransport] using
    (generatedUnifiedMotherAxisTransport_solves_parallelODE
      source 0 1 time)

@[simp] theorem sourceGeneratedMotherTimeTransport_zero
    (source : SmoothUnifiedSource) :
    sourceGeneratedMotherTimeTransport source 0 = 1 := by
  apply Subtype.ext
  change
    (sourceGeneratedMotherTimeTransport source 0 :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) = 1
  rw [sourceGeneratedMotherTimeTransport_coe_eq_axisTransport,
    generatedUnifiedMotherAxisTransport_zero]

theorem sourceGeneratedMotherTimeTransport_add
    (source : SmoothUnifiedSource) (first second : ℝ) :
    sourceGeneratedMotherTimeTransport source (first + second) =
      sourceGeneratedMotherTimeTransport source first *
        sourceGeneratedMotherTimeTransport source second := by
  apply Subtype.ext
  change
    (sourceGeneratedMotherTimeTransport source (first + second) :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) =
      (sourceGeneratedMotherTimeTransport source first :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) *
        (sourceGeneratedMotherTimeTransport source second :
          Matrix SU7MotherIndex SU7MotherIndex ℂ)
  rw [sourceGeneratedMotherTimeTransport_coe_eq_axisTransport,
    sourceGeneratedMotherTimeTransport_coe_eq_axisTransport,
    sourceGeneratedMotherTimeTransport_coe_eq_axisTransport,
    generatedUnifiedMotherAxisTransport_add]

theorem sourceMotherTimeP286Element_add
    (source : SmoothUnifiedSource) (first second : ℝ) :
    sourceMotherTimeP286Element source (first + second) =
      sourceMotherTimeP286Element source first *
        sourceMotherTimeP286Element source second := by
  apply blockDiagonalSMBlock_injective
  simpa only [sourceGeneratedMotherTimeTransport,
    map_mul] using
    (sourceGeneratedMotherTimeTransport_add source first second)

@[simp] theorem sourceMotherTimeP286Element_zero
    (source : SmoothUnifiedSource) :
    sourceMotherTimeP286Element source 0 = 1 := by
  apply blockDiagonalSMBlock_injective
  simpa only [sourceGeneratedMotherTimeTransport,
    map_one] using
    (sourceGeneratedMotherTimeTransport_zero source)

theorem sourceMotherTimeColorElement_add
    (source : SmoothUnifiedSource) (first second : ℝ) :
    sourceMotherTimeColorElement source (first + second) =
      sourceMotherTimeColorElement source first *
        sourceMotherTimeColorElement source second :=
  congrArg Prod.fst
    (sourceMotherTimeP286Element_add source first second)

@[simp] theorem sourceMotherTimeColorElement_zero
    (source : SmoothUnifiedSource) :
    sourceMotherTimeColorElement source 0 = 1 :=
  congrArg Prod.fst (sourceMotherTimeP286Element_zero source)

/-- The typed time transport is a source-generated one-parameter subgroup. -/
def sourceGeneratedMotherTimeTransportFlow
    (source : SmoothUnifiedSource) :
    Multiplicative ℝ →* SU7MotherGroup where
  toFun time := sourceGeneratedMotherTimeTransport source time.toAdd
  map_one' := sourceGeneratedMotherTimeTransport_zero source
  map_mul' first second :=
    sourceGeneratedMotherTimeTransport_add source first.toAdd second.toAdd

theorem positive_sourceGeneratedMotherTimeTransportFlow_nontrivial :
    sourceGeneratedMotherTimeTransportFlow positiveSmoothUnifiedSource ≠ 1 := by
  intro flowIdentity
  apply positive_generatedUnifiedMotherAxisTransport_nonconstant
  funext time
  have typedIdentity := congrArg
    (fun flow : Multiplicative ℝ →* SU7MotherGroup =>
      (flow (Multiplicative.ofAdd time) :
        Matrix SU7MotherIndex SU7MotherIndex ℂ))
    flowIdentity
  have transportIdentity :
      (sourceGeneratedMotherTimeTransport positiveSmoothUnifiedSource time :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) = 1 := by
    simpa [sourceGeneratedMotherTimeTransportFlow] using typedIdentity
  rw [sourceGeneratedMotherTimeTransport_coe_eq_axisTransport] at transportIdentity
  exact transportIdentity

/-! ## Actual P286 color adjoint -/

/-- Conjugation of a color Lie value by an actual `SU(3)` element. -/
def colorGaugeConjugate
    (groupElement : SU3Gauge) (value : SU3BlockLieMatrix) :
    SU3BlockLieMatrix := by
  let groupMatrix : Matrix (Fin 3) (Fin 3) ℂ := groupElement
  refine ⟨groupMatrix * value * star groupMatrix, ?_, ?_⟩
  · rw [star_mul, star_mul, star_star,
      specialUnitaryLieMatrix_star value]
    noncomm_ring
  · have unitary :
        star groupMatrix * groupMatrix = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp
        (Matrix.specialUnitaryGroup_le_unitaryGroup groupElement.property)
    calc
      Matrix.trace
          (groupMatrix * (value : Matrix (Fin 3) (Fin 3) ℂ) *
            star groupMatrix) =
        Matrix.trace
          (((value : Matrix (Fin 3) (Fin 3) ℂ) * star groupMatrix) *
            groupMatrix) := by
          rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = Matrix.trace
          ((value : Matrix (Fin 3) (Fin 3) ℂ) *
            (star groupMatrix * groupMatrix)) := by
          rw [Matrix.mul_assoc]
      _ = Matrix.trace (value : Matrix (Fin 3) (Fin 3) ℂ) := by
          rw [unitary, Matrix.mul_one]
      _ = 0 := value.property.2

@[simp] theorem colorGaugeConjugate_one
    (value : SU3BlockLieMatrix) :
    colorGaugeConjugate 1 value = value := by
  apply Subtype.ext
  simp [colorGaugeConjugate]

theorem colorGaugeConjugate_mul
    (first second : SU3Gauge) (value : SU3BlockLieMatrix) :
    colorGaugeConjugate (first * second) value =
      colorGaugeConjugate first (colorGaugeConjugate second value) := by
  apply Subtype.ext
  simp only [colorGaugeConjugate, Submodule.coe_mk,
    Submonoid.coe_mul, star_mul]
  noncomm_ring

/-- The P286 adjoint induced by the color factor.  Weak and hypercharge
components are fixed because the generated group element has identity in
those factors. -/
def p286ColorGaugeConjugate
    (groupElement : SU3Gauge) (value : P286LieBlockData) :
    P286LieBlockData :=
  (colorGaugeConjugate groupElement value.1, value.2.1, value.2.2)

@[simp] theorem p286ColorGaugeConjugate_one
    (value : P286LieBlockData) :
    p286ColorGaugeConjugate 1 value = value := by
  rcases value with ⟨color, weak, hypercharge⟩
  simp [p286ColorGaugeConjugate]

theorem p286ColorGaugeConjugate_mul
    (first second : SU3Gauge) (value : P286LieBlockData) :
    p286ColorGaugeConjugate (first * second) value =
      p286ColorGaugeConjugate first
        (p286ColorGaugeConjugate second value) := by
  rcases value with ⟨color, weak, hypercharge⟩
  simp [p286ColorGaugeConjugate, colorGaugeConjugate_mul]

set_option maxHeartbeats 1000000 in
/-- The componentwise P286 action is exactly the restriction of the existing
mother `SU(7)` adjoint, not a separately chosen color transformation. -/
theorem p286LieBlockEmbed_p286ColorGaugeConjugate
    (groupElement : SU3Gauge) (value : P286LieBlockData) :
    p286LieBlockEmbed (p286ColorGaugeConjugate groupElement value) =
      motherGaugeConjugate
        (blockDiagonalSMBlock
          ((groupElement, 1, 1) : P286ResidualGaugeGroup))
        (p286LieBlockEmbed value) := by
  apply Subtype.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [p286ColorGaugeConjugate, colorGaugeConjugate,
      motherGaugeConjugate, p286LieBlockEmbed, rawP286LieBlock,
      weakHyperchargeLieBlock, hyperchargeLieBlock, scalarLieBlock,
      blockDiagonalSMBlock, rawBlockDiagonal, weakHyperchargeBlock,
      hyperchargePairBlock, scalarOneBlock, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_two]

def sourceGeneratedMotherTimeP286Adjoint
    (source : SmoothUnifiedSource) (time : ℝ)
    (value : P286LieBlockData) : P286LieBlockData :=
  p286ColorGaugeConjugate
    (sourceMotherTimeColorElement source time) value

@[simp] theorem sourceGeneratedMotherTimeP286Adjoint_zero
    (source : SmoothUnifiedSource) (value : P286LieBlockData) :
    sourceGeneratedMotherTimeP286Adjoint source 0 value = value := by
  rw [sourceGeneratedMotherTimeP286Adjoint,
    sourceMotherTimeColorElement_zero]
  exact p286ColorGaugeConjugate_one value

theorem sourceGeneratedMotherTimeP286Adjoint_add
    (source : SmoothUnifiedSource) (first second : ℝ)
    (value : P286LieBlockData) :
    sourceGeneratedMotherTimeP286Adjoint source (first + second) value =
      sourceGeneratedMotherTimeP286Adjoint source first
        (sourceGeneratedMotherTimeP286Adjoint source second value) := by
  rw [sourceGeneratedMotherTimeP286Adjoint,
    sourceMotherTimeColorElement_add,
    p286ColorGaugeConjugate_mul]
  rfl

/-! ## Primitive holonomic and Cauchy updates -/

/-- Source/path-generated mother-time action on every primitive holonomic
field.  Gravity is fixed by the internal color action; no field is rebuilt
from an equation residual. -/
def sourceGeneratedMotherTimeHolonomicUpdate
    (source : SmoothUnifiedSource) (time : ℝ)
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration where
  coframe := configuration.coframe
  gravityConnection := configuration.gravityConnection
  gravityAuxiliary := configuration.gravityAuxiliary
  gravitySimplicityMultiplier := configuration.gravitySimplicityMultiplier
  gaugeConnection := fun point direction =>
    sourceGeneratedMotherTimeP286Adjoint source time
      (configuration.gaugeConnection point direction)
  gaugeAuxiliary := fun point pair =>
    sourceGeneratedMotherTimeP286Adjoint source time
      (configuration.gaugeAuxiliary point pair)
  scalar := fun point =>
    scalarCoordinateAction
      (sourceGeneratedMotherTimeTransport source time)
      (configuration.scalar point)
  matter := fun point =>
    diracExteriorMatterGaugeRepresentation
      (sourceGeneratedMotherTimeTransport source time)
      (configuration.matter point)
  conjugateMatter := fun point =>
    (configuration.conjugateMatter point).comp
      (diracExteriorMatterGaugeRepresentation
        (sourceGeneratedMotherTimeTransport source time)⁻¹)

@[simp] theorem sourceGeneratedMotherTimeHolonomicUpdate_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    sourceGeneratedMotherTimeHolonomicUpdate source 0 configuration =
      configuration := by
  apply StageNineHolonomicConfiguration.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · funext point direction
    simp [sourceGeneratedMotherTimeHolonomicUpdate]
  · funext point pair
    simp [sourceGeneratedMotherTimeHolonomicUpdate]
  · funext point
    simp [sourceGeneratedMotherTimeHolonomicUpdate]
  · funext point
    change
      diracExteriorMatterGaugeRepresentation
          (sourceGeneratedMotherTimeTransport source 0)
          (configuration.matter point) =
        configuration.matter point
    rw [sourceGeneratedMotherTimeTransport_zero, map_one]
    rfl
  · funext point
    apply LinearMap.ext
    intro matter
    change
      configuration.conjugateMatter point
          (diracExteriorMatterGaugeRepresentation
            (sourceGeneratedMotherTimeTransport source 0)⁻¹ matter) =
        configuration.conjugateMatter point matter
    rw [sourceGeneratedMotherTimeTransport_zero, inv_one, map_one]
    rfl

theorem sourceGeneratedMotherTimeHolonomicUpdate_add
    (source : SmoothUnifiedSource) (first second : ℝ)
    (configuration : StageNineHolonomicConfiguration) :
    sourceGeneratedMotherTimeHolonomicUpdate source (first + second)
        configuration =
      sourceGeneratedMotherTimeHolonomicUpdate source first
        (sourceGeneratedMotherTimeHolonomicUpdate source second
          configuration) := by
  apply StageNineHolonomicConfiguration.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · funext point direction
    exact sourceGeneratedMotherTimeP286Adjoint_add source first second
      (configuration.gaugeConnection point direction)
  · funext point pair
    exact sourceGeneratedMotherTimeP286Adjoint_add source first second
      (configuration.gaugeAuxiliary point pair)
  · funext point
    change
      scalarCoordinateAction
          (sourceGeneratedMotherTimeTransport source (first + second))
          (configuration.scalar point) =
        scalarCoordinateAction
          (sourceGeneratedMotherTimeTransport source first)
          (scalarCoordinateAction
            (sourceGeneratedMotherTimeTransport source second)
            (configuration.scalar point))
    rw [sourceGeneratedMotherTimeTransport_add,
      scalarCoordinateAction_mul]
  · funext point
    change
      diracExteriorMatterGaugeRepresentation
          (sourceGeneratedMotherTimeTransport source (first + second))
          (configuration.matter point) =
        diracExteriorMatterGaugeRepresentation
          (sourceGeneratedMotherTimeTransport source first)
          (diracExteriorMatterGaugeRepresentation
            (sourceGeneratedMotherTimeTransport source second)
            (configuration.matter point))
    rw [sourceGeneratedMotherTimeTransport_add, map_mul]
    rfl
  · funext point
    apply LinearMap.ext
    intro matter
    change
      configuration.conjugateMatter point
          (diracExteriorMatterGaugeRepresentation
            (sourceGeneratedMotherTimeTransport source
              (first + second))⁻¹ matter) =
        configuration.conjugateMatter point
          (diracExteriorMatterGaugeRepresentation
            (sourceGeneratedMotherTimeTransport source second)⁻¹
            (diracExteriorMatterGaugeRepresentation
              (sourceGeneratedMotherTimeTransport source first)⁻¹ matter))
    rw [sourceGeneratedMotherTimeTransport_add, _root_.mul_inv_rev, map_mul]
    rfl

/-- The same actual mother transport acting on pure instantaneous data. -/
def sourceGeneratedMotherTimeCauchyUpdate
    (source : SmoothUnifiedSource) (time : ℝ)
    (state : StageNineCauchyState) : StageNineCauchyState where
  coframe := state.coframe
  gravityConnection := state.gravityConnection
  gravityAuxiliary := state.gravityAuxiliary
  gravitySimplicityMultiplier := state.gravitySimplicityMultiplier
  gaugeConnection := fun space direction =>
    sourceGeneratedMotherTimeP286Adjoint source time
      (state.gaugeConnection space direction)
  gaugeAuxiliary := fun space pair =>
    sourceGeneratedMotherTimeP286Adjoint source time
      (state.gaugeAuxiliary space pair)
  scalar := fun space =>
    scalarCoordinateAction
      (sourceGeneratedMotherTimeTransport source time)
      (state.scalar space)
  scalarVelocity := fun space =>
    scalarCoordinateAction
      (sourceGeneratedMotherTimeTransport source time)
      (state.scalarVelocity space)
  matter := fun space =>
    diracExteriorMatterGaugeRepresentation
      (sourceGeneratedMotherTimeTransport source time)
      (state.matter space)
  conjugateMatter := fun space =>
    (state.conjugateMatter space).comp
      (diracExteriorMatterGaugeRepresentation
        (sourceGeneratedMotherTimeTransport source time)⁻¹)

@[simp] theorem sourceGeneratedMotherTimeCauchyUpdate_zero
    (source : SmoothUnifiedSource) (state : StageNineCauchyState) :
    sourceGeneratedMotherTimeCauchyUpdate source 0 state = state := by
  apply StageNineCauchyState.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · funext space direction
    simp [sourceGeneratedMotherTimeCauchyUpdate]
  · funext space pair
    simp [sourceGeneratedMotherTimeCauchyUpdate]
  · funext space
    simp [sourceGeneratedMotherTimeCauchyUpdate]
  · funext space
    simp [sourceGeneratedMotherTimeCauchyUpdate]
  · funext space
    change
      diracExteriorMatterGaugeRepresentation
          (sourceGeneratedMotherTimeTransport source 0)
          (state.matter space) =
        state.matter space
    rw [sourceGeneratedMotherTimeTransport_zero, map_one]
    rfl
  · funext space
    apply LinearMap.ext
    intro matter
    change
      state.conjugateMatter space
          (diracExteriorMatterGaugeRepresentation
            (sourceGeneratedMotherTimeTransport source 0)⁻¹ matter) =
        state.conjugateMatter space matter
    rw [sourceGeneratedMotherTimeTransport_zero, inv_one, map_one]
    rfl

theorem sourceGeneratedMotherTimeCauchyUpdate_add
    (source : SmoothUnifiedSource) (first second : ℝ)
    (state : StageNineCauchyState) :
    sourceGeneratedMotherTimeCauchyUpdate source (first + second) state =
      sourceGeneratedMotherTimeCauchyUpdate source first
        (sourceGeneratedMotherTimeCauchyUpdate source second state) := by
  apply StageNineCauchyState.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · funext space direction
    exact sourceGeneratedMotherTimeP286Adjoint_add source first second
      (state.gaugeConnection space direction)
  · funext space pair
    exact sourceGeneratedMotherTimeP286Adjoint_add source first second
      (state.gaugeAuxiliary space pair)
  · funext space
    change
      scalarCoordinateAction
          (sourceGeneratedMotherTimeTransport source (first + second))
          (state.scalar space) =
        scalarCoordinateAction
          (sourceGeneratedMotherTimeTransport source first)
          (scalarCoordinateAction
            (sourceGeneratedMotherTimeTransport source second)
            (state.scalar space))
    rw [sourceGeneratedMotherTimeTransport_add,
      scalarCoordinateAction_mul]
  · funext space
    change
      scalarCoordinateAction
          (sourceGeneratedMotherTimeTransport source (first + second))
          (state.scalarVelocity space) =
        scalarCoordinateAction
          (sourceGeneratedMotherTimeTransport source first)
          (scalarCoordinateAction
            (sourceGeneratedMotherTimeTransport source second)
            (state.scalarVelocity space))
    rw [sourceGeneratedMotherTimeTransport_add,
      scalarCoordinateAction_mul]
  · funext space
    change
      diracExteriorMatterGaugeRepresentation
          (sourceGeneratedMotherTimeTransport source (first + second))
          (state.matter space) =
        diracExteriorMatterGaugeRepresentation
          (sourceGeneratedMotherTimeTransport source first)
          (diracExteriorMatterGaugeRepresentation
            (sourceGeneratedMotherTimeTransport source second)
            (state.matter space))
    rw [sourceGeneratedMotherTimeTransport_add, map_mul]
    rfl
  · funext space
    apply LinearMap.ext
    intro matter
    change
      state.conjugateMatter space
          (diracExteriorMatterGaugeRepresentation
            (sourceGeneratedMotherTimeTransport source
              (first + second))⁻¹ matter) =
        state.conjugateMatter space
          (diracExteriorMatterGaugeRepresentation
            (sourceGeneratedMotherTimeTransport source second)⁻¹
            (diracExteriorMatterGaugeRepresentation
              (sourceGeneratedMotherTimeTransport source first)⁻¹ matter))
    rw [sourceGeneratedMotherTimeTransport_add, _root_.mul_inv_rev, map_mul]
    rfl

theorem sourceGeneratedMotherTimeCauchyUpdate_left_inverse
    (source : SmoothUnifiedSource) (time : ℝ)
    (state : StageNineCauchyState) :
    sourceGeneratedMotherTimeCauchyUpdate source (-time)
        (sourceGeneratedMotherTimeCauchyUpdate source time state) = state := by
  calc
    sourceGeneratedMotherTimeCauchyUpdate source (-time)
        (sourceGeneratedMotherTimeCauchyUpdate source time state) =
      sourceGeneratedMotherTimeCauchyUpdate source (-time + time) state :=
        (sourceGeneratedMotherTimeCauchyUpdate_add source (-time) time
          state).symm
    _ = state := by simp

theorem sourceGeneratedMotherTimeCauchyUpdate_right_inverse
    (source : SmoothUnifiedSource) (time : ℝ)
    (state : StageNineCauchyState) :
    sourceGeneratedMotherTimeCauchyUpdate source time
        (sourceGeneratedMotherTimeCauchyUpdate source (-time) state) = state := by
  calc
    sourceGeneratedMotherTimeCauchyUpdate source time
        (sourceGeneratedMotherTimeCauchyUpdate source (-time) state) =
      sourceGeneratedMotherTimeCauchyUpdate source (time + -time) state :=
        (sourceGeneratedMotherTimeCauchyUpdate_add source time (-time)
          state).symm
    _ = state := by simp

def sourceGeneratedMotherTimeCauchyEquiv
    (source : SmoothUnifiedSource) (time : ℝ) :
    Equiv.Perm StageNineCauchyState where
  toFun := sourceGeneratedMotherTimeCauchyUpdate source time
  invFun := sourceGeneratedMotherTimeCauchyUpdate source (-time)
  left_inv := sourceGeneratedMotherTimeCauchyUpdate_left_inverse source time
  right_inv := sourceGeneratedMotherTimeCauchyUpdate_right_inverse source time

/-- The complete instantaneous update as a source/path-generated
one-parameter automorphism flow. -/
def sourceGeneratedMotherTimeCauchyFlow
    (source : SmoothUnifiedSource) :
    Multiplicative ℝ →* Equiv.Perm StageNineCauchyState where
  toFun time := sourceGeneratedMotherTimeCauchyEquiv source time.toAdd
  map_one' := by
    apply Equiv.ext
    intro state
    exact sourceGeneratedMotherTimeCauchyUpdate_zero source state
  map_mul' := by
    intro first second
    apply Equiv.ext
    intro state
    exact sourceGeneratedMotherTimeCauchyUpdate_add source first.toAdd
      second.toAdd state

/-- Restricting the holonomic action gives exactly the Cauchy update, including
the scalar time derivative. -/
theorem canonicalCauchyRestriction_motherTimeUpdate
    (source : SmoothUnifiedSource) (transportTime sliceTime : ℝ)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    canonicalCauchyRestriction sliceTime
        (sourceGeneratedMotherTimeHolonomicUpdate source transportTime
          configuration) =
      sourceGeneratedMotherTimeCauchyUpdate source transportTime
        (canonicalCauchyRestriction sliceTime configuration) := by
  rcases smooth with
    ⟨_, _, _, _, _, _, scalarSmooth, _, _⟩
  apply StageNineCauchyState.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext space
    exact fieldDirectionalDerivative_scalarCoordinateAction
      (sourceGeneratedMotherTimeTransport source transportTime)
      configuration.scalar
      (canonicalCauchySlicePoint sliceTime space)
      canonicalLorentzianTimeDirection
      ((scalarSmooth.differentiable (by simp)).differentiableAt)
  · rfl
  · rfl

/-- The path time at which the source color-Cartan transport makes a canonical
quarter turn.  It is derived from the already fixed source coefficient; no
new source parameter or constitutive coupling is introduced. -/
def sourceMotherCanonicalQuarterTurnTime
    (source : SmoothUnifiedSource) : ℝ :=
  Real.pi / (2 * source.legacy.sigma)

theorem sourceMotherTimeColorPhase_canonicalQuarterTurn
    (source : SmoothUnifiedSource) :
    ((sourceMotherTimeColorPhase source
        (sourceMotherCanonicalQuarterTurnTime source) : Circle) : ℂ) =
      -Complex.I := by
  rw [sourceMotherTimeColorPhase, Circle.coe_exp]
  have sigmaNonzero :
      source.legacy.sigma ≠ 0 :=
    ne_of_gt source.legacy.sigma_pos
  have argument :
      -source.legacy.sigma *
          sourceMotherCanonicalQuarterTurnTime source =
        -(Real.pi / 2) := by
    unfold sourceMotherCanonicalQuarterTurnTime
    field_simp [sigmaNonzero]
  rw [argument, Complex.exp_ofReal_mul_I]
  simp

theorem sourceMotherCanonicalQuarterTurn_colorMixing_entry
    (source : SmoothUnifiedSource) :
    ((colorGaugeConjugate
        (sourceMotherTimeColorElement source
          (sourceMotherCanonicalQuarterTurnTime source))
        colorMixingGenerator : SU3BlockLieMatrix) :
      Matrix (Fin 3) (Fin 3) ℂ) 0 1 = -1 := by
  simp [colorGaugeConjugate, sourceMotherTimeColorElement,
    sourceMotherTimeColorMatrix, colorMixingGenerator, colorMixingRaw,
    Matrix.mul_apply, Fin.sum_univ_three,
    sourceMotherTimeColorPhase_canonicalQuarterTurn]

theorem sourceMotherCanonicalQuarterTurn_p286Adjoint_nontrivial
    (source : SmoothUnifiedSource) :
    sourceGeneratedMotherTimeP286Adjoint source
        (sourceMotherCanonicalQuarterTurnTime source)
        (colorMixingGenerator, 0, 0) ≠
      (colorMixingGenerator, 0, 0) := by
  intro adjointFixed
  have entryFixed := congrArg
    (fun value : P286LieBlockData =>
      ((value.1 : SU3BlockLieMatrix) :
        Matrix (Fin 3) (Fin 3) ℂ) 0 1)
    adjointFixed
  rw [sourceGeneratedMotherTimeP286Adjoint,
    p286ColorGaugeConjugate] at entryFixed
  rw [sourceMotherCanonicalQuarterTurn_colorMixing_entry] at entryFixed
  norm_num [colorMixingGenerator, colorMixingRaw] at entryFixed

def positiveMotherTimeColorMixingProbeState : StageNineCauchyState :=
  { positivePhaseProbeCauchyState with
    gaugeConnection := fun _ direction =>
      if direction = canonicalLorentzianTimeDirection then
        (colorMixingGenerator, 0, 0)
      else
        0 }

/-- Positive regression on the actual instantaneous carrier: the generated
non-Abelian path changes a primitive P286 connection value. -/
theorem positive_sourceGeneratedMotherTimeCauchyUpdate_nontrivial :
    sourceGeneratedMotherTimeCauchyUpdate positiveSmoothUnifiedSource
        (sourceMotherCanonicalQuarterTurnTime positiveSmoothUnifiedSource)
        positiveMotherTimeColorMixingProbeState ≠
      positiveMotherTimeColorMixingProbeState := by
  intro updateFixed
  have connectionFixed := congrArg
    (fun state : StageNineCauchyState =>
      state.gaugeConnection 0 canonicalLorentzianTimeDirection)
    updateFixed
  apply sourceMotherCanonicalQuarterTurn_p286Adjoint_nontrivial
    positiveSmoothUnifiedSource
  simpa [sourceGeneratedMotherTimeCauchyUpdate,
    positiveMotherTimeColorMixingProbeState] using connectionFixed

theorem positive_sourceGeneratedMotherTimeCauchyFlow_nontrivial :
    sourceGeneratedMotherTimeCauchyFlow positiveSmoothUnifiedSource ≠ 1 := by
  intro flowIdentity
  have probeFixed := congrArg
    (fun flow : Multiplicative ℝ →* Equiv.Perm StageNineCauchyState =>
      flow
        (Multiplicative.ofAdd
          (sourceMotherCanonicalQuarterTurnTime
            positiveSmoothUnifiedSource))
        positiveMotherTimeColorMixingProbeState)
    flowIdentity
  apply positive_sourceGeneratedMotherTimeCauchyUpdate_nontrivial
  simpa [sourceGeneratedMotherTimeCauchyFlow,
    sourceGeneratedMotherTimeCauchyEquiv] using probeFixed

/-- Identity-path negative control: removing path length in the time
parameter leaves every primitive Cauchy datum unchanged. -/
theorem sourceGeneratedMotherTimeCauchyFlow_identityPath
    (source : SmoothUnifiedSource) (state : StageNineCauchyState) :
    sourceGeneratedMotherTimeCauchyFlow source 1 state = state :=
  sourceGeneratedMotherTimeCauchyUpdate_zero source state

end

end SaturationMonoid.PhysicsCore.StageNineSourceGeneratedMotherTimeCauchyFlow
