import H0mework.Physics.Source.SourceBridgeNoGo
import H0mework.Physics.Source.ProofFreeSource
import H0mework.Physics.Matter.SU7ExteriorMatterRestriction
import H0mework.Physics.Gauge.SU7MotherGaugeConnection
import H0mework.Realization.Residual.Algebra
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Stage-9 enriched proof-free source and S9-0 producer bridges

The old source stores only an integer phase cochain.  The retained
`StageNineSourceBridgeNoGo` proves that this finite sampling cannot determine a
continuous unitary flow.  This module makes the minimal source enrichment: one
real continuous-contact residual.  It is not a connection, curvature,
holonomy, Hamiltonian, state, or certificate.

The existing source `sigma` splits that residual into keep and trace parts.
The trace part is the common rate from which this module computes both:

* an actual smooth-entry SU(7) transition cocycle, mother potential, curvature,
  and rectangular holonomy;
* an actual continuous complex-unitary one-parameter flow whose samples equal
  the generated source phase transport.

All bridge data are pinned to definitions and all laws are proved here.  The
positive source has nonzero curvature, nontrivial holonomy, and nontrivial
unitary evolution.  The zero-residual source is the flat/identity negative
regression.  Forgetting the new residual returns the old source and therefore
still triggers the old typed no-go.
-/

namespace SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource

open ProofFreeRicherAnholonomicSource
open StageNineSourceBridgeNoGo
open StageEightProofFreeSource
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open GaugeProjection
open GaugeProjection.ConcreteBlockDiagonal
open AffineRelaxation
open RepresentationArithmeticAtomProjectionDefect
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StandardModelConstraint

noncomputable section

/-- Minimal Stage-9 enrichment.  The sole new datum is a continuous contact
residual; all geometric and quantum objects remain outputs. -/
structure SmoothUnifiedSource where
  stageEight : StageEightProofFreeSource.Source
  continuousContactResidual : ℝ

/-- Forget exactly the enrichment and recover the old proof-free source. -/
def SmoothUnifiedSource.forget
    (source : SmoothUnifiedSource) :
    ProofFreeRicherAnholonomicSource.Source :=
  source.stageEight.toPhysicalSource

/-- The old source projection is kept as a readout so the retained S9-0
no-go remains literally applicable. -/
abbrev SmoothUnifiedSource.legacy
    (source : SmoothUnifiedSource) :
    ProofFreeRicherAnholonomicSource.Source :=
  source.forget

/-- The actual linear keep operator on the continuous residual carrier. -/
def SmoothUnifiedSource.continuousKeep
    (source : SmoothUnifiedSource) : ℝ →ₗ[ℝ] ℝ :=
  scalarKeepLinearMap source.legacy.sigma

/-- Residual that remains untransported at the current contact. -/
def SmoothUnifiedSource.continuousResidualKeep
    (source : SmoothUnifiedSource) : ℝ :=
  source.continuousKeep source.continuousContactResidual

/-- The uniquely forced complementary trace `(I - K)r`. -/
def SmoothUnifiedSource.continuousResidualTrace
    (source : SmoothUnifiedSource) : ℝ :=
  linearResidualTrace source.continuousKeep source.continuousContactResidual

/-- The common continuous rate is generated from the scalar trace share, not
stored as a Hamiltonian or connection coefficient.  The completed trace is a
structural carrier defined after the two producer closures below. -/
def SmoothUnifiedSource.continuousContactRate
    (source : SmoothUnifiedSource) : ℝ :=
  source.continuousResidualTrace

/-- The continuous residual obeys the same keep/trace conservation split as
the framework root law. -/
theorem SmoothUnifiedSource.continuousResidual_split
    (source : SmoothUnifiedSource) :
    source.continuousContactResidual =
      source.continuousResidualKeep + source.continuousResidualTrace := by
  exact residualTransportCore_residual_split
    source.continuousKeep source.continuousContactResidual

@[simp] theorem SmoothUnifiedSource.continuousResidualKeep_eq_scalar
    (source : SmoothUnifiedSource) :
    source.continuousResidualKeep =
      (1 - source.legacy.sigma) * source.continuousContactResidual := by
  simp [continuousResidualKeep, continuousKeep, scalarKeepLinearMap]

@[simp] theorem SmoothUnifiedSource.continuousResidualTrace_eq_scalar
    (source : SmoothUnifiedSource) :
    source.continuousResidualTrace =
      source.legacy.sigma * source.continuousContactResidual := by
  simpa [continuousResidualTrace, continuousKeep] using
    (residualTransportCore_scalar_trace
      source.legacy.sigma source.continuousContactResidual)

@[simp] theorem SmoothUnifiedSource.continuousContactRate_eq_scalar
    (source : SmoothUnifiedSource) :
    source.continuousContactRate =
      source.legacy.sigma * source.continuousContactResidual := by
  simp [continuousContactRate]

/-- Trace is not an independent source slot: any proposed complement satisfying
the split is definitionally forced to the residual-core trace. -/
theorem SmoothUnifiedSource.continuousResidual_trace_unique
    (source : SmoothUnifiedSource) (trace : ℝ) :
    source.continuousContactResidual =
        source.continuousResidualKeep + trace ↔
      trace = source.continuousResidualTrace := by
  exact residualTransportCore_trace_unique
    source.continuousKeep source.continuousContactResidual trace

/-- The old source already proves `sigma > 0`, so the enriched scalar keep is
an active/faithful residual transport. -/
theorem SmoothUnifiedSource.continuousKeep_active
    (source : SmoothUnifiedSource) :
    ResidualTransportActive source.continuousKeep := by
  exact scalarKeepLinearMap_active_of_ne_zero
    source.legacy.sigma (ne_of_gt source.legacy.sigma_pos)

def continuousResidualEnergy (residual : ℝ) : ℝ := residual ^ 2

theorem continuousResidualEnergy_eq_zero_iff (residual : ℝ) :
    continuousResidualEnergy residual = 0 ↔ residual = 0 := by
  simp [continuousResidualEnergy]

/-- Faithful transport ties fixedness, zero residual, zero trace, and zero
energy on the exact continuous residual carrier. -/
theorem SmoothUnifiedSource.continuousTransport_equivalence
    (source : SmoothUnifiedSource) (residual : ℝ) :
    ResidualTransportFixed source.continuousKeep residual ↔
      residual = 0 ∧
        linearResidualTrace source.continuousKeep residual = 0 ∧
        continuousResidualEnergy residual = 0 :=
  residualTransportCore_fixed_iff_zero_residual_trace_energy
    source.continuousKeep continuousResidualEnergy
    source.continuousKeep_active continuousResidualEnergy_eq_zero_iff residual

/-! ## Continuous phase/unitary producer -/

/-- Continuous unitary dynamics generated from the common trace rate. -/
def generatedUnitaryFlow
    (source : SmoothUnifiedSource) :
    ComplexUnitaryOneParameterFlow where
  evolve := fun time => Circle.exp (source.continuousContactRate * time)
  evolve_zero := by simp
  evolve_add := by
    intro first second
    rw [mul_add, Circle.exp_add]
  continuous_evolve :=
    Circle.exp.continuous.comp
      (continuous_const.mul continuous_id)

/-- Complex phase transport generated from the enriched rate and the old
exact integer phase edge. -/
def generatedPhaseTransport
    (source : SmoothUnifiedSource)
    (initial terminal : Sum ThreeCycleTime ThreeCycleTime) : Circle :=
  Circle.exp
    (source.continuousContactRate *
      (source.legacy.phaseCochain initial terminal : ℝ))

theorem generatedUnitaryFlow_samples_phaseTransport
    (source : SmoothUnifiedSource) (initial terminal) :
    (generatedUnitaryFlow source).evolve
        (source.legacy.phaseCochain initial terminal : ℝ) =
      generatedPhaseTransport source initial terminal :=
  rfl

/-! ## Smooth SU(7) geometric producer -/

abbrev StageNineChart := Fin 3

def chartWeight (chart : StageNineChart) : ℝ := chart

/-- Actual SU(7)-valued transition on the three-chart generated cover. -/
def generatedTransition
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (point : BasePoint) : SU7MotherGroup :=
  embeddedP286HyperchargeElement
    (Circle.exp
      ((chartWeight terminal - chartWeight initial) *
        source.continuousContactRate * point 0))

theorem embeddedP286HyperchargeElement_mul (first second : Circle) :
    embeddedP286HyperchargeElement (first * second) =
      embeddedP286HyperchargeElement first *
        embeddedP286HyperchargeElement second := by
  change blockDiagonalSMBlock (p286HyperchargeElement (first * second)) =
    blockDiagonalSMBlock (p286HyperchargeElement first) *
      blockDiagonalSMBlock (p286HyperchargeElement second)
  rw [show p286HyperchargeElement (first * second) =
      p286HyperchargeElement first * p286HyperchargeElement second by
        ext <;> simp [p286HyperchargeElement]]
  exact blockDiagonalSMBlock.map_mul _ _

@[simp] theorem embeddedP286HyperchargeElement_one :
    embeddedP286HyperchargeElement 1 = 1 := by
  change blockDiagonalSMBlock (p286HyperchargeElement 1) = 1
  rw [show p286HyperchargeElement 1 = 1 by rfl]
  exact blockDiagonalSMBlock.map_one

theorem generatedTransition_normalized
    (source : SmoothUnifiedSource)
    (chart : StageNineChart) (point : BasePoint) :
    generatedTransition source chart chart point = 1 := by
  simp [generatedTransition]

/-- The cocycle law is a theorem of the generated transition functions. -/
theorem generatedTransition_cocycle
    (source : SmoothUnifiedSource)
    (first second third : StageNineChart) (point : BasePoint) :
    generatedTransition source second third point *
        generatedTransition source first second point =
      generatedTransition source first third point := by
  unfold generatedTransition
  rw [← embeddedP286HyperchargeElement_mul]
  rw [← Circle.exp_add]
  congr 2
  ring

/-- Smoothness of an actual SU(7)-valued field, stated entrywise to avoid
adding a decorative normed structure on the matrix subtype. -/
def SU7FieldComponentwiseSmooth
    (field : BasePoint → SU7MotherGroup) : Prop :=
  ∀ row column,
    ContDiff ℝ ⊤
      (fun point => ((field point :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) row column))

theorem complexExpPhase_componentwiseSmooth
    (chartDelta sigma residual : ℂ) :
    ContDiff ℝ ⊤
      (fun point : BasePoint =>
        Complex.exp
          (chartDelta * (sigma * residual) *
            (point 0 : ℂ) * Complex.I)) := by
  apply Complex.contDiff_exp.comp
  exact
    (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp
        (by fun_prop : ContDiff ℝ ⊤ (fun point : BasePoint => point 0)))).mul
      contDiff_const

theorem generatedTransition_componentwiseSmooth
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart) :
    SU7FieldComponentwiseSmooth
      (generatedTransition source initial terminal) := by
  intro row column
  have hphase := complexExpPhase_componentwiseSmooth
    ((chartWeight terminal : ℂ) - (chartWeight initial : ℂ))
    (source.legacy.sigma : ℂ) (source.continuousContactResidual : ℂ)
  have hphaseInv := hphase.inv (fun point => Complex.exp_ne_zero _)
  fin_cases row <;> fin_cases column <;>
    simp [generatedTransition, embeddedP286HyperchargeElement,
      p286HyperchargeElement, blockDiagonalSMBlock, rawBlockDiagonal,
      weakHyperchargeBlock, hyperchargePairBlock, scalarOneBlock,
      chartWeight] <;>
    first | exact hphase | exact hphaseInv | fun_prop

/-- The actual mother-Lie direction tangent to the embedded hypercharge
circle. -/
def motherHyperchargeDirection : SU7MotherLieMatrix :=
  p286LieBlockEmbed (0, 0, hyperchargeGenerator)

/-- A global smooth mother potential generated from the trace rate.  Only the
`1` direction is nonzero, and it varies with coordinate `0`. -/
def generatedMotherPotential
    (source : SmoothUnifiedSource)
    (point : BasePoint) (direction : LorentzianIndex) :
    SU7MotherLieMatrix :=
  if direction = 1 then
    (source.continuousContactRate * point 0) • motherHyperchargeDirection
  else 0

/-- Curvature of the generated affine potential. -/
def generatedMotherCurvature
    (source : SmoothUnifiedSource)
    (first second : LorentzianIndex) : SU7MotherLieMatrix :=
  if first = 0 ∧ second = 1 then
    source.continuousContactRate • motherHyperchargeDirection
  else if first = 1 ∧ second = 0 then
    (-source.continuousContactRate) • motherHyperchargeDirection
  else 0

/-- Exact affine increment law that produces the `01` exterior derivative. -/
theorem generatedMotherPotential_increment
    (source : SmoothUnifiedSource) (point displacement : BasePoint) :
    generatedMotherPotential source (point + displacement) 1 =
      generatedMotherPotential source point 1 +
        (source.continuousContactRate * displacement 0) •
          motherHyperchargeDirection := by
  simp [generatedMotherPotential, mul_add, add_smul]

def MotherPotentialComponentwiseSmooth
    (source : SmoothUnifiedSource) : Prop :=
  ∀ direction row column,
    ContDiff ℝ ⊤
      (fun point =>
        ((generatedMotherPotential source point direction :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) row column))

theorem complexLinearCoordinate_componentwiseSmooth
    (sigma residual : ℝ) :
    ContDiff ℝ ⊤
      (fun point : BasePoint =>
        (sigma : ℂ) * (residual : ℂ) *
          (point 0 : ℂ) * Complex.I) := by
  exact
    ((contDiff_const.mul contDiff_const).mul
      (Complex.ofRealCLM.contDiff.comp
        (by fun_prop : ContDiff ℝ ⊤ (fun point : BasePoint => point 0)))).mul
      contDiff_const

theorem generatedMotherPotential_componentwiseSmooth
    (source : SmoothUnifiedSource) :
    MotherPotentialComponentwiseSmooth source := by
  intro direction row column
  have hcoordinate :=
    complexLinearCoordinate_componentwiseSmooth
      source.legacy.sigma source.continuousContactResidual
  fin_cases direction <;> fin_cases row <;> fin_cases column <;>
    simp [generatedMotherPotential, motherHyperchargeDirection,
      p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
      hyperchargeLieBlock, scalarLieBlock, hyperchargeGenerator] <;>
    first | exact hcoordinate | exact hcoordinate.neg | fun_prop

@[simp] theorem generatedMotherCurvature_zero_one
    (source : SmoothUnifiedSource) :
    generatedMotherCurvature source 0 1 =
      source.continuousContactRate • motherHyperchargeDirection := by
  simp [generatedMotherCurvature]

/-- Rectangle holonomy produced by exponentiating the generated curvature
flux in the actual embedded SU(7) subgroup. -/
def generatedRectangleHolonomy
    (source : SmoothUnifiedSource) (area : ℝ) : SU7MotherGroup :=
  embeddedP286HyperchargeElement
    (Circle.exp (source.continuousContactRate * area))

theorem embeddedP286HyperchargeElement_injective :
    Function.Injective embeddedP286HyperchargeElement := by
  intro first second heq
  have hp286 : p286HyperchargeElement first =
      p286HyperchargeElement second := by
    exact blockDiagonalSMBlock_injective heq
  exact congrArg (fun value : StandardModelGaugeGroup => value.2.2) hp286

/-! ## Positive and negative source regressions -/

def positiveSmoothUnifiedSource : SmoothUnifiedSource where
  stageEight := canonicalSource
  continuousContactResidual := 2 * Real.pi

/-- The enriched root now preserves the actual Stage-8 P506/L0 producer
instead of reintroducing an external lineage certificate downstream. -/
theorem positiveSmoothUnifiedSource_generates_exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  canonicalSource_generates_exactP506L0Lineage

@[simp] theorem positiveSmoothUnifiedSource_generates_endpoint_eleven :
    positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
        canonicalSource_generatedLineage_height_pos = 11 :=
  canonicalSource_generates_selectedEndpoint_eleven

@[simp] theorem positive_continuousContactRate :
    positiveSmoothUnifiedSource.continuousContactRate = Real.pi := by
  norm_num [positiveSmoothUnifiedSource, SmoothUnifiedSource.legacy,
    SmoothUnifiedSource.forget, StageEightProofFreeSource.Source.toPhysicalSource,
    ProofFreeRicherAnholonomicSource.Source.sigma, canonicalSource]
  ring

theorem positive_generatedUnitaryFlow_nontrivial :
    (generatedUnitaryFlow positiveSmoothUnifiedSource).evolve 1 ≠ 1 := by
  change Circle.exp (positiveSmoothUnifiedSource.continuousContactRate * 1) ≠ 1
  rw [positive_continuousContactRate, mul_one]
  exact Circle.exp_pi_ne_one

theorem positive_generatedRectangleHolonomy_nontrivial :
    generatedRectangleHolonomy positiveSmoothUnifiedSource 1 ≠ 1 := by
  intro heq
  rw [generatedRectangleHolonomy,
    positive_continuousContactRate, mul_one] at heq
  have hembedOne :
      embeddedP286HyperchargeElement (Circle.exp Real.pi) =
        embeddedP286HyperchargeElement 1 := by
    simpa using heq
  exact Circle.exp_pi_ne_one
    (embeddedP286HyperchargeElement_injective hembedOne)

theorem motherHyperchargeDirection_hyperPlus_entry :
    (motherHyperchargeDirection :
      Matrix SU7MotherIndex SU7MotherIndex ℂ)
        hyperPlusIndex hyperPlusIndex = Complex.I := by
  simp [motherHyperchargeDirection, p286LieBlockEmbed, rawP286LieBlock,
    weakHyperchargeLieBlock, hyperchargeLieBlock, scalarLieBlock,
    hyperchargeGenerator, hyperPlusIndex]

theorem positive_generatedMotherCurvature_hyperPlus_entry :
    (generatedMotherCurvature positiveSmoothUnifiedSource 0 1 :
      Matrix SU7MotherIndex SU7MotherIndex ℂ)
        hyperPlusIndex hyperPlusIndex = (Real.pi : ℂ) * Complex.I := by
  rw [generatedMotherCurvature_zero_one, positive_continuousContactRate]
  simp [motherHyperchargeDirection_hyperPlus_entry]

theorem positive_generatedMotherCurvature_nonzero :
    generatedMotherCurvature positiveSmoothUnifiedSource 0 1 ≠ 0 := by
  intro hzero
  have hentry := congrArg
    (fun curvature : SU7MotherLieMatrix =>
      (curvature : Matrix SU7MotherIndex SU7MotherIndex ℂ)
        hyperPlusIndex hyperPlusIndex) hzero
  rw [positive_generatedMotherCurvature_hyperPlus_entry] at hentry
  simp at hentry

def zeroRateSmoothUnifiedSource : SmoothUnifiedSource where
  stageEight := canonicalSource
  continuousContactResidual := 0

@[simp] theorem zeroRate_continuousContactRate :
    zeroRateSmoothUnifiedSource.continuousContactRate = 0 := by
  simp [zeroRateSmoothUnifiedSource]

@[simp] theorem zeroRate_generatedMotherCurvature :
    generatedMotherCurvature zeroRateSmoothUnifiedSource 0 1 = 0 := by
  rw [generatedMotherCurvature_zero_one, zeroRate_continuousContactRate]
  simp

@[simp] theorem zeroRate_generatedRectangleHolonomy :
    generatedRectangleHolonomy zeroRateSmoothUnifiedSource 1 = 1 := by
  rw [generatedRectangleHolonomy, zeroRate_continuousContactRate]
  simp

/-- The enrichment is invisible under the old source projection. -/
theorem zeroRate_positive_forget_eq :
    zeroRateSmoothUnifiedSource.forget =
      positiveSmoothUnifiedSource.forget :=
  rfl

/-- The new residual nevertheless separates the generated continuous flows. -/
theorem zeroRate_positive_generatedFlows_distinct :
    generatedUnitaryFlow zeroRateSmoothUnifiedSource ≠
      generatedUnitaryFlow positiveSmoothUnifiedSource := by
  intro heq
  have hone := congrArg (fun flow => flow.evolve 1) heq
  change Circle.exp (zeroRateSmoothUnifiedSource.continuousContactRate * 1) =
    Circle.exp (positiveSmoothUnifiedSource.continuousContactRate * 1) at hone
  rw [zeroRate_continuousContactRate,
    positive_continuousContactRate] at hone
  have hphase : (1 : Circle) = Circle.exp Real.pi := by
    simpa using hone
  exact Circle.exp_pi_ne_one hphase.symm

/-- Required persistent negative regression: forgetting the enrichment restores
the old typed no-go. -/
theorem forgottenSource_still_fails_oldS9ZeroGate
    (source : SmoothUnifiedSource) :
    ¬ StageNineS9ZeroCurrentSourceGate source.forget :=
  currentSource_stageNineS9Zero_typedNoGo source.forget

/-! ## S9-0 generated bridge credentials -/

structure SourceGeneratedGeometricBridge
    (source : SmoothUnifiedSource) where
  transition : StageNineChart → StageNineChart →
    BasePoint → SU7MotherGroup
  transition_eq : transition = generatedTransition source
  transition_normalized : ∀ chart point,
    transition chart chart point = 1
  transition_cocycle : ∀ first second third point,
    transition second third point * transition first second point =
      transition first third point
  transition_componentwiseSmooth : ∀ initial terminal,
    SU7FieldComponentwiseSmooth (transition initial terminal)
  potential : BasePoint → LorentzianIndex → SU7MotherLieMatrix
  potential_eq : potential = generatedMotherPotential source
  potential_componentwiseSmooth : MotherPotentialComponentwiseSmooth source
  potential_increment : ∀ point displacement,
    potential (point + displacement) 1 = potential point 1 +
      (source.continuousContactRate * displacement 0) •
        motherHyperchargeDirection
  curvature : LorentzianIndex → LorentzianIndex → SU7MotherLieMatrix
  curvature_eq : curvature = generatedMotherCurvature source
  curvature_zero_one : curvature 0 1 =
    source.continuousContactRate • motherHyperchargeDirection
  rectangleHolonomy : ℝ → SU7MotherGroup
  rectangleHolonomy_eq : rectangleHolonomy =
    generatedRectangleHolonomy source

def sourceGeneratedGeometricBridge
    (source : SmoothUnifiedSource) :
    SourceGeneratedGeometricBridge source where
  transition := generatedTransition source
  transition_eq := rfl
  transition_normalized := generatedTransition_normalized source
  transition_cocycle := generatedTransition_cocycle source
  transition_componentwiseSmooth :=
    generatedTransition_componentwiseSmooth source
  potential := generatedMotherPotential source
  potential_eq := rfl
  potential_componentwiseSmooth :=
    generatedMotherPotential_componentwiseSmooth source
  potential_increment := generatedMotherPotential_increment source
  curvature := generatedMotherCurvature source
  curvature_eq := rfl
  curvature_zero_one := generatedMotherCurvature_zero_one source
  rectangleHolonomy := generatedRectangleHolonomy source
  rectangleHolonomy_eq := rfl

structure SourceGeneratedContinuousPhaseBridge
    (source : SmoothUnifiedSource) where
  flow : ComplexUnitaryOneParameterFlow
  flow_eq : flow = generatedUnitaryFlow source
  phaseTransport : Sum ThreeCycleTime ThreeCycleTime →
    Sum ThreeCycleTime ThreeCycleTime → Circle
  phaseTransport_eq : phaseTransport = generatedPhaseTransport source
  flow_samples_phaseTransport : ∀ initial terminal,
    flow.evolve (source.legacy.phaseCochain initial terminal : ℝ) =
      phaseTransport initial terminal

def sourceGeneratedContinuousPhaseBridge
    (source : SmoothUnifiedSource) :
    SourceGeneratedContinuousPhaseBridge source where
  flow := generatedUnitaryFlow source
  flow_eq := rfl
  phaseTransport := generatedPhaseTransport source
  phaseTransport_eq := rfl
  flow_samples_phaseTransport :=
    generatedUnitaryFlow_samples_phaseTransport source

/-- Producer closure generated from the obstruction carried by the unresolved
continuous residual.  Both outputs remain indexed by the exact same source. -/
structure SourceGeneratedBridgeClosure
    (source : SmoothUnifiedSource) where
  geometric : SourceGeneratedGeometricBridge source
  quantumPhase : SourceGeneratedContinuousPhaseBridge source

def sourceGeneratedBridgeClosure
    (source : SmoothUnifiedSource) :
    SourceGeneratedBridgeClosure source where
  geometric := sourceGeneratedGeometricBridge source
  quantumPhase := sourceGeneratedContinuousPhaseBridge source

/-- Structural trace written back after producer closure.  This is not a log:
it carries the geometry and continuous phase structures that have actually
been generated, together with the remaining residual and its conservation
law. -/
structure SourceGeneratedTraceCarrier
    (source : SmoothUnifiedSource) where
  keep : ℝ →ₗ[ℝ] ℝ
  keep_eq : keep = source.continuousKeep
  transportActive : ResidualTransportActive keep
  residualKeep : ℝ
  residualKeep_eq : residualKeep = keep source.continuousContactResidual
  residualTraceShare : ℝ
  residualTraceShare_eq : residualTraceShare =
    linearResidualTrace keep source.continuousContactResidual
  traceUnique : ∀ trace : ℝ,
    source.continuousContactResidual = residualKeep + trace ↔
      trace = residualTraceShare
  closure : SourceGeneratedBridgeClosure source
  residualConservation :
    source.continuousContactResidual = residualKeep + residualTraceShare
  fixedZeroTraceEnergy : ∀ residual : ℝ,
    ResidualTransportFixed keep residual ↔
      residual = 0 ∧ linearResidualTrace keep residual = 0 ∧
        continuousResidualEnergy residual = 0

/-- Trace write-back produced from the source contact and bridge closure. -/
def sourceGeneratedTraceWriteBack
    (source : SmoothUnifiedSource) :
    SourceGeneratedTraceCarrier source where
  keep := source.continuousKeep
  keep_eq := rfl
  transportActive := source.continuousKeep_active
  residualKeep := source.continuousKeep source.continuousContactResidual
  residualKeep_eq := rfl
  residualTraceShare :=
    linearResidualTrace source.continuousKeep source.continuousContactResidual
  residualTraceShare_eq := rfl
  traceUnique := fun trace =>
    source.continuousResidual_trace_unique trace
  closure := sourceGeneratedBridgeClosure source
  residualConservation := source.continuousResidual_split
  fixedZeroTraceEnergy := source.continuousTransport_equivalence

/-- S9-0 consumes the structural trace write-back rather than treating the
scalar trace share as a log or accepting two independent bridge receipts. -/
structure StageNineS9ZeroBridgeCredential
    (source : SmoothUnifiedSource) where
  writeBack : SourceGeneratedTraceCarrier source
  writeBack_eq : writeBack = sourceGeneratedTraceWriteBack source

def sourceGeneratedStageNineS9ZeroBridgeCredential
    (source : SmoothUnifiedSource) :
    StageNineS9ZeroBridgeCredential source where
  writeBack := sourceGeneratedTraceWriteBack source
  writeBack_eq := rfl

/-- S9-0 positive close: one enriched proof-free source produces both bridges
and all three required nontrivial witnesses.  This is a checkpoint, not the
Stage-9 root credential. -/
theorem positiveSource_generates_nontrivial_S9ZeroBridge :
    Nonempty (StageNineS9ZeroBridgeCredential positiveSmoothUnifiedSource) ∧
      positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
          canonicalSource_generatedLineage_height_pos = 11 ∧
      generatedMotherCurvature positiveSmoothUnifiedSource 0 1 ≠ 0 ∧
      generatedRectangleHolonomy positiveSmoothUnifiedSource 1 ≠ 1 ∧
      (generatedUnitaryFlow positiveSmoothUnifiedSource).evolve 1 ≠ 1 :=
  ⟨⟨sourceGeneratedStageNineS9ZeroBridgeCredential
      positiveSmoothUnifiedSource⟩,
    positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
    positiveSmoothUnifiedSource_generates_endpoint_eleven,
    positive_generatedMotherCurvature_nonzero,
    positive_generatedRectangleHolonomy_nontrivial,
    positive_generatedUnitaryFlow_nontrivial⟩

end

end SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource
