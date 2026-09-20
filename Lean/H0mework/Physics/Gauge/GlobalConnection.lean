import H0mework.Physics.Geometry.GlobalBundle
import H0mework.Physics.Lorentz.PointwiseLorentzSpinConnectionRecovery

/-!
# Stage-9A source-generated global connection and path holonomy

The nonconstant transition generated at S9-0 now acts on chart-local mother
potentials.  Each local potential is computed from the common source rate and
the chart weight.  Their overlap law, including the inhomogeneous logarithmic
derivative, is proved rather than supplied.  All chart curvatures descend to
the same nonzero global curvature.

The same source coframe generates a pointwise Lorentz spin-connection field.
For the canonical positive source every point is nondegenerate, so the tetrad
postulate and Lorentz-skew law hold pointwise.  Smooth spin descent and the
formal `SL(2,ℂ) → SO⁺(1,3)` cover map remain open.

Finally an explicit coordinate-segment parallel transport is generated from
the connection and its endpoint around the source rectangle is proved equal
to the earlier flux holonomy.  This replaces the S9-0 exponential readout by
an actual path-transport theorem on the generated affine connection.
-/

namespace SaturationMonoid.PhysicsCore.StageNineGlobalConnection

open ProofFreeRicherAnholonomicSource
open PointwiseLorentzianCoframeJet
open SU7MotherLieAlgebra
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7MotherGaugeTheory
open GaugeProjection
open GaugeProjection.ConcreteBlockDiagonal
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalBundle

noncomputable section

/-! ## Chart-local mother connection and overlap descent -/

def generatedLocalMotherCoefficient
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (direction : LorentzianIndex) : ℝ :=
  (if direction = 1 then source.continuousContactRate * point 0 else 0) -
    if direction = 0 then chartWeight chart * source.continuousContactRate
    else 0

def generatedLocalMotherPotential
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (direction : LorentzianIndex) :
    SU7MotherLieMatrix :=
  generatedLocalMotherCoefficient source chart point direction •
    motherHyperchargeDirection

def generatedTransitionDerivativeCoefficient
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (direction : LorentzianIndex) : ℝ :=
  if direction = 0 then
    (chartWeight terminal - chartWeight initial) *
      source.continuousContactRate
  else 0

def generatedTransitionLogDerivative
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (direction : LorentzianIndex) : SU7MotherLieMatrix :=
  generatedTransitionDerivativeCoefficient source initial terminal direction •
    motherHyperchargeDirection

theorem generatedLocalMotherCoefficient_overlap
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (point : BasePoint) (direction : LorentzianIndex) :
    generatedLocalMotherCoefficient source terminal point direction =
      generatedLocalMotherCoefficient source initial point direction -
        generatedTransitionDerivativeCoefficient source initial terminal
          direction := by
  by_cases direction_zero : direction = 0
  · subst direction
    simp [generatedLocalMotherCoefficient,
      generatedTransitionDerivativeCoefficient]
    ring
  · simp [generatedLocalMotherCoefficient,
      generatedTransitionDerivativeCoefficient, direction_zero]

/-- The Abelian overlap law before exposing the adjoint action. -/
theorem generatedLocalMotherPotential_overlap_linear
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (point : BasePoint) (direction : LorentzianIndex) :
    generatedLocalMotherPotential source terminal point direction =
      generatedLocalMotherPotential source initial point direction -
        generatedTransitionLogDerivative source initial terminal direction := by
  change
    generatedLocalMotherCoefficient source terminal point direction •
        motherHyperchargeDirection =
      generatedLocalMotherCoefficient source initial point direction •
          motherHyperchargeDirection -
        generatedTransitionDerivativeCoefficient source initial terminal
            direction • motherHyperchargeDirection
  calc
    _ = (generatedLocalMotherCoefficient source initial point direction -
          generatedTransitionDerivativeCoefficient source initial terminal
            direction) • motherHyperchargeDirection := by
        rw [generatedLocalMotherCoefficient_overlap]
    _ = _ := by module

def motherAdjointMatrix
    (groupElement : SU7MotherGroup) (value : SU7MotherLieMatrix) :
    Matrix SU7MotherIndex SU7MotherIndex ℂ :=
  (groupElement : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
    (value : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
      ((groupElement⁻¹ : SU7MotherGroup) :
        Matrix SU7MotherIndex SU7MotherIndex ℂ)

theorem embeddedP286HyperchargeElement_commutes_motherHyperchargeDirection
    (phase : Circle) :
    (embeddedP286HyperchargeElement phase :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) *
        (motherHyperchargeDirection :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) =
      (motherHyperchargeDirection :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) *
        (embeddedP286HyperchargeElement phase :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [embeddedP286HyperchargeElement, p286HyperchargeElement,
      blockDiagonalSMBlock, rawBlockDiagonal, weakHyperchargeBlock,
      hyperchargePairBlock, scalarOneBlock, motherHyperchargeDirection,
      p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
      hyperchargeLieBlock, scalarLieBlock, hyperchargeGenerator,
      Matrix.mul_apply] <;> ring

theorem embeddedP286HyperchargeElement_adjoint_motherHyperchargeDirection
    (phase : Circle) :
    motherAdjointMatrix (embeddedP286HyperchargeElement phase)
        motherHyperchargeDirection =
      (motherHyperchargeDirection :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) := by
  rw [motherAdjointMatrix,
    embeddedP286HyperchargeElement_commutes_motherHyperchargeDirection]
  rw [Matrix.mul_assoc]
  change
    (motherHyperchargeDirection :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) *
        (((embeddedP286HyperchargeElement phase) *
          (embeddedP286HyperchargeElement phase)⁻¹ : SU7MotherGroup) :
            Matrix SU7MotherIndex SU7MotherIndex ℂ) = _
  rw [mul_inv_cancel]
  simp

theorem motherAdjointMatrix_real_smul
    (groupElement : SU7MotherGroup) (coefficient : ℝ)
    (value : SU7MotherLieMatrix) :
    motherAdjointMatrix groupElement (coefficient • value) =
      (coefficient : ℂ) • motherAdjointMatrix groupElement value := by
  change
    (groupElement : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
          ((coefficient : ℂ) •
            (value : Matrix SU7MotherIndex SU7MotherIndex ℂ)) *
        ((groupElement⁻¹ : SU7MotherGroup) :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) =
      (coefficient : ℂ) •
        ((groupElement : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
          (value : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
          ((groupElement⁻¹ : SU7MotherGroup) :
            Matrix SU7MotherIndex SU7MotherIndex ℂ))
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem generatedTransition_adjoint_localMotherPotential
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (point : BasePoint) (direction : LorentzianIndex) :
    motherAdjointMatrix (generatedTransition source initial terminal point)
        (generatedLocalMotherPotential source initial point direction) =
      (generatedLocalMotherPotential source initial point direction :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) := by
  rw [generatedLocalMotherPotential, motherAdjointMatrix_real_smul]
  change
    (generatedLocalMotherCoefficient source initial point direction : ℂ) •
        motherAdjointMatrix
          (generatedTransition source initial terminal point)
          motherHyperchargeDirection =
      (generatedLocalMotherCoefficient source initial point direction : ℂ) •
        (motherHyperchargeDirection :
          Matrix SU7MotherIndex SU7MotherIndex ℂ)
  rw [generatedTransition,
    embeddedP286HyperchargeElement_adjoint_motherHyperchargeDirection]

/-- Full local gauge overlap law in the ambient matrix carrier. -/
theorem generatedLocalMotherPotential_overlap_gauge
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (point : BasePoint) (direction : LorentzianIndex) :
    (generatedLocalMotherPotential source terminal point direction :
        Matrix SU7MotherIndex SU7MotherIndex ℂ) =
      motherAdjointMatrix (generatedTransition source initial terminal point)
          (generatedLocalMotherPotential source initial point direction) -
        (generatedTransitionLogDerivative source initial terminal direction :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) := by
  rw [generatedTransition_adjoint_localMotherPotential]
  exact congrArg Subtype.val
    (generatedLocalMotherPotential_overlap_linear source initial terminal
      point direction)

/-- The affine increment is independent of chart; constant gauge-frame shifts
do not change the generated exterior derivative. -/
theorem generatedLocalMotherPotential_increment
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point displacement : BasePoint) :
    generatedLocalMotherPotential source chart (point + displacement) 1 =
      generatedLocalMotherPotential source chart point 1 +
        (source.continuousContactRate * displacement 0) •
          motherHyperchargeDirection := by
  simp [generatedLocalMotherPotential, generatedLocalMotherCoefficient,
    mul_add, add_smul]

/-- Every local chart computes the same global mother curvature. -/
def generatedLocalMotherCurvature
    (source : SmoothUnifiedSource) (_chart : StageNineChart)
    (first second : LorentzianIndex) : SU7MotherLieMatrix :=
  generatedMotherCurvature source first second

theorem generatedLocalMotherCurvature_descends
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (first second : LorentzianIndex) :
    generatedLocalMotherCurvature source initial first second =
      generatedLocalMotherCurvature source terminal first second :=
  rfl

/-! ## Source-generated Lorentz connection field -/

def generatedLorentzConnectionAt
    (source : SmoothUnifiedSource) (point : BasePoint) :
    PointwiseLorentzSpinConnection :=
  (source.legacy.jetAt point).lorentzSpinConnection

theorem positive_generatedLorentzConnection_lorentzSkew
    (point : BasePoint) :
    LorentzSkew
      (generatedLorentzConnectionAt positiveSmoothUnifiedSource point) := by
  exact
    (canonicalPhysicalSource.jetAt point).lorentzSpinConnection_lorentzSkew
      (canonicalPhysicalSource_globally_nondegenerate point)

theorem positive_generatedLorentzConnection_tetradCompatible
    (point : BasePoint) :
    TetradCompatible (canonicalPhysicalSource.jetAt point)
      (canonicalPhysicalSource.jetAt point).leviCivitaConnection
      (generatedLorentzConnectionAt positiveSmoothUnifiedSource point) := by
  exact (canonicalPhysicalSource.jetAt point).leviCivita_lorentzSpinConnection_tetradCompatible
      (canonicalPhysicalSource_globally_nondegenerate point)

/-! ## Actual coordinate-path transport -/

def generatedVerticalPath
    (x0 length time : ℝ) : BasePoint :=
  EuclideanSpace.single 0 x0 +
    EuclideanSpace.single 1 (length * time)

@[simp] theorem generatedVerticalPath_zeroCoordinate
    (x0 length time : ℝ) :
    generatedVerticalPath x0 length time 0 = x0 := by
  simp [generatedVerticalPath]

/-- The connection coefficient along the generated vertical path is constant
and is exactly the generator exponentiated below. -/
theorem generatedLocalMotherPotential_verticalPath
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (x0 length time : ℝ) :
    generatedLocalMotherPotential source chart
        (generatedVerticalPath x0 length time) 1 =
      (source.continuousContactRate * x0) •
        motherHyperchargeDirection := by
  simp [generatedLocalMotherPotential, generatedLocalMotherCoefficient,
    generatedVerticalPath]

/-- Parallel transport along the coordinate-`1` segment of length `length`
at fixed coordinate `x0`, parameterized by `time`. -/
def generatedVerticalParallelTransport
    (source : SmoothUnifiedSource)
    (x0 length time : ℝ) : SU7MotherGroup :=
  embeddedP286HyperchargeElement
    (Circle.exp (source.continuousContactRate * x0 * length * time))

@[simp] theorem generatedVerticalParallelTransport_zero
    (source : SmoothUnifiedSource) (x0 length : ℝ) :
    generatedVerticalParallelTransport source x0 length 0 = 1 := by
  simp [generatedVerticalParallelTransport]

theorem generatedVerticalParallelTransport_add
    (source : SmoothUnifiedSource) (x0 length first second : ℝ) :
    generatedVerticalParallelTransport source x0 length (first + second) =
      generatedVerticalParallelTransport source x0 length first *
        generatedVerticalParallelTransport source x0 length second := by
  rw [generatedVerticalParallelTransport,
    generatedVerticalParallelTransport,
    generatedVerticalParallelTransport,
    mul_add, Circle.exp_add, embeddedP286HyperchargeElement_mul]

/-- The endpoint transport around the generated coordinate rectangle equals
the source-generated curvature-flux holonomy. -/
theorem generatedRectanglePathTransport_eq_holonomy
    (source : SmoothUnifiedSource) (width height : ℝ) :
    generatedVerticalParallelTransport source width height 1 =
      generatedRectangleHolonomy source (width * height) := by
  unfold generatedVerticalParallelTransport generatedRectangleHolonomy
  congr 2
  ring

theorem positive_generatedRectanglePathTransport_nontrivial :
    generatedVerticalParallelTransport positiveSmoothUnifiedSource 1 1 1 ≠
      1 := by
  rw [generatedRectanglePathTransport_eq_holonomy]
  simpa using positive_generatedRectangleHolonomy_nontrivial

@[simp] theorem zeroRate_generatedLocalMotherPotential
    (chart : StageNineChart) (point : BasePoint)
    (direction : LorentzianIndex) :
    generatedLocalMotherPotential zeroRateSmoothUnifiedSource chart
        point direction = 0 := by
  rw [generatedLocalMotherPotential]
  unfold generatedLocalMotherCoefficient
  rw [zeroRate_continuousContactRate]
  simp

@[simp] theorem zeroRate_generatedVerticalParallelTransport
    (x0 length time : ℝ) :
    generatedVerticalParallelTransport zeroRateSmoothUnifiedSource
        x0 length time = 1 := by
  rw [generatedVerticalParallelTransport, zeroRate_continuousContactRate]
  simp

/-- Flat-source negative regression: erasing the contact trace erases every
local mother potential and every coordinate-path transport. -/
theorem zeroRateSource_connection_and_pathTransport_trivial :
    (∀ chart point direction,
      generatedLocalMotherPotential zeroRateSmoothUnifiedSource chart
        point direction = 0) ∧
      (∀ x0 length time,
        generatedVerticalParallelTransport zeroRateSmoothUnifiedSource
          x0 length time = 1) :=
  ⟨zeroRate_generatedLocalMotherPotential,
    zeroRate_generatedVerticalParallelTransport⟩

/-- S9-A2 checkpoint: local connection overlap descent, pointwise Lorentz
connection generation, and nontrivial path holonomy are outputs of one source.
This still does not close associated bundles or smooth spin descent. -/
theorem positiveSource_generates_connectionDescent_and_pathHolonomy :
    (∀ initial terminal point direction,
      (generatedLocalMotherPotential positiveSmoothUnifiedSource terminal
          point direction : Matrix SU7MotherIndex SU7MotherIndex ℂ) =
        motherAdjointMatrix
            (generatedTransition positiveSmoothUnifiedSource initial terminal
              point)
            (generatedLocalMotherPotential positiveSmoothUnifiedSource initial
              point direction) -
          (generatedTransitionLogDerivative positiveSmoothUnifiedSource
            initial terminal direction :
              Matrix SU7MotherIndex SU7MotherIndex ℂ)) ∧
      (∀ point,
        LorentzSkew
          (generatedLorentzConnectionAt positiveSmoothUnifiedSource point)) ∧
      generatedMotherCurvature positiveSmoothUnifiedSource 0 1 ≠ 0 ∧
      generatedVerticalParallelTransport
          positiveSmoothUnifiedSource 1 1 1 ≠ 1 := by
  exact ⟨generatedLocalMotherPotential_overlap_gauge
      positiveSmoothUnifiedSource,
    positive_generatedLorentzConnection_lorentzSkew,
    positive_generatedMotherCurvature_nonzero,
    positive_generatedRectanglePathTransport_nontrivial⟩

end

end SaturationMonoid.PhysicsCore.StageNineGlobalConnection
