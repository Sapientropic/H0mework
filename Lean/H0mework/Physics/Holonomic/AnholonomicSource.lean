import H0mework.Physics.Lorentz.PointwiseLorentzGeometryOutput
import H0mework.Physics.Geometry.PlebanskiReductionCoherence
import H0mework.Physics.Admission.SU7SourcePhaseFieldAnchorCore
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Proof-free richer source and anholonomic Lorentz geometry

This module is the source/geometry foundation for PhysicsCore Stage 4.  The
raw source stores only A6 path coordinates, a phase amplitude, a sigma seed,
a color scale, and first-order coframe deformation coefficients.  It stores no
tetrad, metric, Hodge map, connection, curvature, stationary solution,
coupling, field equation, or final credential.

From those coordinates it computes:

* a nonzero-capable exact phase trace with componentwise closed H1 ledger;
* `0 < sigma < 1` and a trace-exact color field;
* a smooth affine, potentially anholonomic coframe field;
* its Lorentzian metric and nondegenerate origin geometry;
* the existing torsion-free metric-compatible affine/spin output;
* the physical 36-component substitution `B = *internal(e ∧ e)`;
* the affine-metric two-jet curvature at the origin.

The physical substitution is quadratic and changes carrier dimension from 16
to 36, so it cannot be the previous identity surrogate.  This module does not
yet define the common BF--Plebanski/Yang--Mills action or claim continuum
Einstein recovery.
-/

namespace SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource

open GeneratedEndpointQuadraticCoframeSource
open SU7RicherLineageResponsibility
open StandardModelConstraint
open scoped Matrix.Norms.Elementwise

noncomputable section

abbrev BasePoint := EuclideanSpace ℝ LorentzianIndex

/-- Raw source coordinates only.  No tetrad, metric, Hodge, connection,
curvature, stationary point, coupling, equation, or admission certificate is
stored here. -/
structure Source where
  sourceRoot : SU7A6WeightLabel
  sourceMoves : SourcePathData
  phaseAmplitude : Int
  sigmaSeed : Nat
  colorScale : Nat
  coframeLinearCoefficient : LorentzianCoframeDerivative

namespace Source

def phasePotential (source : Source) :
    Sum ThreeCycleTime ThreeCycleTime → Int
  | Sum.inl ThreeCycleTime.t0 => 0
  | Sum.inl ThreeCycleTime.t1 => source.phaseAmplitude
  | Sum.inl ThreeCycleTime.t2 => 2 * source.phaseAmplitude
  | Sum.inr ThreeCycleTime.t0 => 0
  | Sum.inr ThreeCycleTime.t1 => -source.phaseAmplitude
  | Sum.inr ThreeCycleTime.t2 => source.phaseAmplitude

def phaseCochain (source : Source) : ComponentPhaseCochain :=
  fun initial terminal =>
    source.phasePotential terminal - source.phasePotential initial

theorem phaseCochain_h1Closed (source : Source) :
    ComponentH1Closed source.phaseCochain := by
  simp [ComponentH1Closed, componentH1Ledger, phaseCochain,
    phasePotential, threeAgentRingResidual, leftSelectedCochain,
    rightSelectedCochain]

theorem phaseCochain_nontrivial
    (source : Source) (hamplitude : source.phaseAmplitude ≠ 0) :
    source.phaseCochain (Sum.inl ThreeCycleTime.t0)
        (Sum.inl ThreeCycleTime.t1) ≠ 0 := by
  simpa [phaseCochain, phasePotential] using hamplitude

def sigma (source : Source) : ℝ :=
  1 / (source.sigmaSeed + 2 : ℝ)

theorem sigma_pos (source : Source) : 0 < source.sigma := by
  simp [sigma]
  positivity

theorem sigma_lt_one (source : Source) : source.sigma < 1 := by
  apply (div_lt_one (by positivity)).2
  have hseed : (0 : ℝ) ≤ (source.sigmaSeed : ℝ) := by positivity
  linarith

def field (source : Source) : ColorLoopField :=
  rawCodeColorLoopMatrix source.colorScale
    source.colorScale source.colorScale

theorem field_traceExact (source : Source) :
    ColorLoopTraceExact source.field := by
  apply (rawCodeColorLoop_traceExact_iff_balance
    source.colorScale source.colorScale source.colorScale).mpr
  omega

def anchor (source : Source) : SourcePhaseFieldAnchor where
  sourceRoot := source.sourceRoot
  sourcePathData := source.sourceMoves
  sourcePath :=
    SU7A6GaugeStableRootGraphAdapter.reachableFrom_zero
      source.sourceRoot source.sourceMoves source.sourceMoves
  phaseCochain := source.phaseCochain
  h1Closed := source.phaseCochain_h1Closed
  sigma := source.sigma
  field := source.field

/-- Generated affine coframe field.  The constant identity frame is fixed by
the grammar; the source stores only its raw first-order deformation
coefficients. -/
def coframeAt (source : Source) (point : BasePoint) : LorentzianCoframe :=
  Matrix.of fun internal coordinate =>
    (1 : LorentzianCoframe) internal coordinate +
      ∑ direction : LorentzianIndex,
        source.coframeLinearCoefficient direction internal coordinate *
          point direction

def coframeIncrement
    (source : Source) (displacement : BasePoint) : LorentzianCoframe :=
  Matrix.of fun internal coordinate =>
    ∑ direction : LorentzianIndex,
      source.coframeLinearCoefficient direction internal coordinate *
        displacement direction

theorem coframeAt_add
    (source : Source) (point displacement : BasePoint) :
    source.coframeAt (point + displacement) =
      source.coframeAt point + source.coframeIncrement displacement := by
  ext internal coordinate
  change
    (1 : LorentzianCoframe) internal coordinate +
          ∑ direction : LorentzianIndex,
            source.coframeLinearCoefficient direction internal coordinate *
              (point direction + displacement direction) =
      ((1 : LorentzianCoframe) internal coordinate +
          ∑ direction : LorentzianIndex,
            source.coframeLinearCoefficient direction internal coordinate *
              point direction) +
        ∑ direction : LorentzianIndex,
          source.coframeLinearCoefficient direction internal coordinate *
            displacement direction
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring

theorem coframeAt_contDiff (source : Source) :
    ContDiff ℝ ⊤ source.coframeAt := by
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  unfold coframeAt
  simp only [Matrix.of_apply]
  fun_prop

def jetAt
    (source : Source) (point : BasePoint) :
    PointwiseLorentzianCoframeJet where
  coframe := source.coframeAt point
  derivative := source.coframeLinearCoefficient

@[simp] theorem coframeAt_zero (source : Source) :
    source.coframeAt 0 = 1 := by
  ext internal coordinate
  simp [coframeAt]

@[simp] theorem jetAt_zero_coframe (source : Source) :
    (source.jetAt 0).coframe = 1 :=
  source.coframeAt_zero

theorem jetAt_zero_nondegenerate (source : Source) :
    Matrix.det (source.jetAt 0).coframe ≠ 0 := by
  simp

def geometryAtOrigin (source : Source) :
    PointwiseLorentzGeometryOutput (source.jetAt 0) :=
  producePointwiseLorentzGeometryFromJet
    (source.jetAt 0) source.jetAt_zero_nondegenerate

/-- Native nondegenerate domain of the generated smooth coframe field. -/
abbrev NondegenerateDomain (source : Source) :=
  { point : BasePoint // Matrix.det (source.coframeAt point) ≠ 0 }

def geometryAt
    (source : Source) (point : source.NondegenerateDomain) :
    PointwiseLorentzGeometryOutput (source.jetAt point.1) :=
  producePointwiseLorentzGeometryFromJet
    (source.jetAt point.1) point.2

def metricAt (source : Source) (point : BasePoint) : LorentzianMetric :=
  lorentzianMetricOfCoframe (source.coframeAt point)

theorem metricAt_contDiff (source : Source) :
    ContDiff ℝ ⊤ source.metricAt := by
  have hcoframe (internal coordinate : LorentzianIndex) :
      ContDiff ℝ ⊤ (fun point => source.coframeAt point internal coordinate) :=
    contDiff_pi.mp (contDiff_pi.mp source.coframeAt_contDiff internal) coordinate
  apply contDiff_pi'
  intro first
  apply contDiff_pi'
  intro second
  simp only [metricAt, lorentzianMetricOfCoframe, Matrix.mul_apply,
    Matrix.transpose_apply]
  apply ContDiff.sum
  intro middle _
  apply ContDiff.mul
  · apply ContDiff.sum
    intro internal _
    exact (hcoframe internal first).mul contDiff_const
  · exact hcoframe middle second

def metricSecondDerivative
    (source : Source)
    (firstDirection secondDirection first second : LorentzianIndex) : ℝ :=
  ∑ internal, minkowskiInternalSign internal *
    (source.coframeLinearCoefficient firstDirection internal first *
        source.coframeLinearCoefficient secondDirection internal second +
      source.coframeLinearCoefficient secondDirection internal first *
        source.coframeLinearCoefficient firstDirection internal second)

def inverseMetricDerivativeAt
    (source : Source) (point : source.NondegenerateDomain)
    (direction first second : LorentzianIndex) : ℝ :=
  -∑ firstContracted,
    ∑ secondContracted,
      ((source.jetAt point.1).metric)⁻¹ first firstContracted *
        (source.jetAt point.1).metricDerivative direction
          firstContracted secondContracted *
        ((source.jetAt point.1).metric)⁻¹ secondContracted second

def loweredChristoffelDerivativeAt
    (source : Source)
    (derivativeDirection loweredIndex first second : LorentzianIndex) : ℝ :=
  (source.metricSecondDerivative derivativeDirection first second loweredIndex +
      source.metricSecondDerivative derivativeDirection second first loweredIndex -
      source.metricSecondDerivative derivativeDirection loweredIndex first second) /
    2

def raisedChristoffelDerivativeAt
    (source : Source) (point : source.NondegenerateDomain)
    (derivativeDirection upper first second : LorentzianIndex) : ℝ :=
  ∑ loweredIndex, (
    source.inverseMetricDerivativeAt point derivativeDirection upper loweredIndex *
        (source.jetAt point.1).loweredLeviCivitaConnection loweredIndex first second +
      ((source.jetAt point.1).metric)⁻¹ upper loweredIndex *
        source.loweredChristoffelDerivativeAt derivativeDirection
          loweredIndex first second)

/-- Levi-Civita Riemann curvature computed across the native nondegenerate
domain from the generated affine coframe two-jet. -/
def coordinateCurvatureAt
    (source : Source) (point : source.NondegenerateDomain)
    (upper lower first second : LorentzianIndex) : ℝ :=
  source.raisedChristoffelDerivativeAt point first upper second lower -
      source.raisedChristoffelDerivativeAt point second upper first lower +
    ∑ middle,
      ((source.jetAt point.1).leviCivitaConnection upper first middle *
          (source.jetAt point.1).leviCivitaConnection middle second lower -
        (source.jetAt point.1).leviCivitaConnection upper second middle *
          (source.jetAt point.1).leviCivitaConnection middle first lower)

theorem coordinateCurvatureAt_antisymm
    (source : Source) (point : source.NondegenerateDomain)
    (upper lower first second : LorentzianIndex) :
    source.coordinateCurvatureAt point upper lower first second =
      -source.coordinateCurvatureAt point upper lower second first := by
  unfold coordinateCurvatureAt
  have hsum :
      (∑ middle,
        ((source.jetAt point.1).leviCivitaConnection upper first middle *
            (source.jetAt point.1).leviCivitaConnection middle second lower -
          (source.jetAt point.1).leviCivitaConnection upper second middle *
            (source.jetAt point.1).leviCivitaConnection middle first lower)) =
        -∑ middle,
          ((source.jetAt point.1).leviCivitaConnection upper second middle *
              (source.jetAt point.1).leviCivitaConnection middle first lower -
            (source.jetAt point.1).leviCivitaConnection upper first middle *
              (source.jetAt point.1).leviCivitaConnection middle second lower) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro middle _
    ring
  rw [hsum]
  ring

abbrev CoordinateCurvatureField :=
  LorentzianIndex → LorentzianIndex →
    LorentzianIndex → LorentzianIndex → ℝ

def coordinateCurvatureField
    (source : Source) :
    source.NondegenerateDomain → CoordinateCurvatureField :=
  fun point => source.coordinateCurvatureAt point

/-- Coordinate anholonomy `∂_μ eᴬ_ν - ∂_ν eᴬ_μ`, computed from raw
source coefficients. -/
def anholonomy
    (source : Source)
    (internal first second : LorentzianIndex) : ℝ :=
  source.coframeLinearCoefficient first internal second -
    source.coframeLinearCoefficient second internal first

def IsAnholonomic (source : Source) : Prop :=
  ∃ internal first second, source.anholonomy internal first second ≠ 0

end Source

def shearCoefficient : LorentzianCoframeDerivative :=
  fun direction internal coordinate =>
    if direction = 2 ∧ internal = 0 ∧ coordinate = 1 then 1 else 0

def positiveSource : Source where
  sourceRoot := 0
  sourceMoves := 0
  phaseAmplitude := 1
  sigmaSeed := 0
  colorScale := 1
  coframeLinearCoefficient := shearCoefficient

theorem positiveSource_phase_nontrivial :
    positiveSource.phaseCochain (Sum.inl ThreeCycleTime.t0)
        (Sum.inl ThreeCycleTime.t1) ≠ 0 := by
  exact positiveSource.phaseCochain_nontrivial (by norm_num [positiveSource])

theorem positiveSource_h1Closed :
    ComponentH1Closed positiveSource.phaseCochain :=
  positiveSource.phaseCochain_h1Closed

theorem positiveSource_sigma : positiveSource.sigma = 1 / 2 := by
  norm_num [Source.sigma, positiveSource]

theorem positiveSource_field_nonzero : positiveSource.field ≠ 0 := by
  intro hzero
  have hentry := congrFun (congrFun hzero 0) 0
  norm_num [Source.field, positiveSource, rawCodeColorLoopMatrix] at hentry

theorem positiveSource_anholonomic : positiveSource.IsAnholonomic := by
  refine ⟨0, 2, 1, ?_⟩
  simp [Source.anholonomy, positiveSource, shearCoefficient]

theorem positiveSource_geometry_nondegenerate :
    Matrix.det (positiveSource.jetAt 0).coframe ≠ 0 :=
  positiveSource.jetAt_zero_nondegenerate

theorem positiveSource_coframeAt_eq_transvection (point : BasePoint) :
    positiveSource.coframeAt point =
      Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
        (point 2) := by
  ext internal coordinate
  fin_cases internal <;> fin_cases coordinate <;>
    simp [Source.coframeAt, positiveSource, shearCoefficient,
      Matrix.transvection, Matrix.single]

theorem positiveSource_coframeAt_det (point : BasePoint) :
    Matrix.det (positiveSource.coframeAt point) = 1 := by
  rw [positiveSource_coframeAt_eq_transvection]
  exact Matrix.det_transvection_of_ne 0 1 (by norm_num) (point 2)

theorem positiveSource_globally_nondegenerate (point : BasePoint) :
    Matrix.det (positiveSource.coframeAt point) ≠ 0 := by
  rw [positiveSource_coframeAt_det]
  norm_num

def positiveSourceDomainPoint (point : BasePoint) :
    positiveSource.NondegenerateDomain :=
  ⟨point, positiveSource_globally_nondegenerate point⟩

/-! ## Physical `II+` bivector substitution -/

/-- Oriented pair order `(01, 02, 03, 23, 31, 12)`. -/
def pairFirst : Fin 6 → LorentzianIndex :=
  ![0, 0, 0, 2, 3, 1]

def pairSecond : Fin 6 → LorentzianIndex :=
  ![1, 2, 3, 3, 1, 2]

abbrev PhysicalBivector := Fin 6 → Fin 6 → ℝ

/-- The actual coframe wedge `eᴵ ∧ eʲ`, with internal-pair and
spacetime-pair coordinates kept distinct. -/
def coframeWedge (coframe : LorentzianCoframe) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    coframe (pairFirst internalPair) (pairFirst spacetimePair) *
        coframe (pairSecond internalPair) (pairSecond spacetimePair) -
      coframe (pairFirst internalPair) (pairSecond spacetimePair) *
        coframe (pairSecond internalPair) (pairFirst spacetimePair)

/-- Lorentzian internal Hodge dual applied independently at every spacetime
two-form coordinate. -/
def internalBivectorDual (bivector : PhysicalBivector) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    lorentzianCoframeHodge
      (fun sourceInternalPair => bivector sourceInternalPair spacetimePair)
      internalPair

/-- Physical gravitational `II+` bivector `*(e ∧ e)`. -/
def physicalIIPlusBivector
    (coframe : LorentzianCoframe) : PhysicalBivector :=
  internalBivectorDual (coframeWedge coframe)

def physicalRawIIPlusSubstitution :
    RawPlebanskiIIPlusSubstitution PhysicalBivector LorentzianCoframe where
  tetradWedge := coframeWedge
  internalBivectorDual := internalBivectorDual

@[simp] theorem physicalRawIIPlusSubstitution_apply
    (coframe : LorentzianCoframe) :
    physicalRawIIPlusSubstitution.gravitationalBivector coframe =
      physicalIIPlusBivector coframe :=
  rfl

theorem coframeWedge_smul
    (scalar : ℝ) (coframe : LorentzianCoframe) :
    coframeWedge (scalar • coframe) =
      scalar ^ 2 • coframeWedge coframe := by
  funext internalPair spacetimePair
  simp [coframeWedge]
  ring

theorem physicalIIPlusBivector_smul
    (scalar : ℝ) (coframe : LorentzianCoframe) :
    physicalIIPlusBivector (scalar • coframe) =
      scalar ^ 2 • physicalIIPlusBivector coframe := by
  unfold physicalIIPlusBivector
  rw [coframeWedge_smul]
  funext internalPair spacetimePair
  fin_cases internalPair <;>
    simp [internalBivectorDual, lorentzianCoframeHodge, Pi.smul_apply]

@[simp] theorem physicalIIPlusBivector_identity_component :
    physicalIIPlusBivector (1 : LorentzianCoframe) 3 0 = -1 := by
  change -((1 : LorentzianCoframe) 0 0 * (1 : LorentzianCoframe) 1 1 -
      (1 : LorentzianCoframe) 0 1 * (1 : LorentzianCoframe) 1 0) = -1
  norm_num

theorem physicalIIPlusBivector_not_zero :
    physicalIIPlusBivector (1 : LorentzianCoframe) ≠ 0 := by
  intro hzero
  have hcomponent := congrFun (congrFun hzero 3) 0
  norm_num at hcomponent

/-- The physical substitution cannot be the old identity surrogate even up to
a linear change of coordinates: tetrads have 16 components, while the
internal-bivector-valued spacetime two-form has 36. -/
theorem no_linear_identity_surrogate :
    ¬ Nonempty (LorentzianCoframe ≃ₗ[ℝ] PhysicalBivector) := by
  rintro ⟨equivalence⟩
  have hfinrank := LinearEquiv.finrank_eq equivalence
  have hcoframe : Module.finrank ℝ LorentzianCoframe = 16 := by
    change Module.finrank ℝ (Matrix (Fin 4) (Fin 4) ℝ) = 16
    rw [Module.finrank_matrix]
    norm_num
  have hbivector : Module.finrank ℝ PhysicalBivector = 36 := by
    change Module.finrank ℝ (Matrix (Fin 6) (Fin 6) ℝ) = 36
    rw [Module.finrank_matrix]
    norm_num
  omega

theorem positiveSource_generates_physicalIIPlus :
    physicalRawIIPlusSubstitution.gravitationalBivector
        (positiveSource.jetAt 0).coframe =
      physicalIIPlusBivector (positiveSource.jetAt 0).coframe :=
  rfl

/-- Field-level producer theorem.  Smoothness, nondegeneracy, metric/Hodge,
torsion-free spin data, physical `II+`, and curvature all come from the same
raw source coefficients. -/
theorem Source.generates_smoothLorentzGeometry
    (source : Source) (point : source.NondegenerateDomain) :
    ContDiff ℝ ⊤ source.coframeAt ∧
      ContDiff ℝ ⊤ source.metricAt ∧
      Matrix.det (source.jetAt point.1).coframe ≠ 0 ∧
      (source.geometryAt point).metric = (source.jetAt point.1).metric ∧
      (source.geometryAt point).hodge = lorentzianCoframeHodge ∧
      PointwiseLorentzianCoframeJet.TorsionFree
        (source.geometryAt point).spin.affineConnection ∧
      TetradCompatible (source.jetAt point.1)
        (source.geometryAt point).spin.affineConnection
        (source.geometryAt point).spin.spinConnection ∧
      physicalRawIIPlusSubstitution.gravitationalBivector
          (source.jetAt point.1).coframe =
        physicalIIPlusBivector (source.jetAt point.1).coframe ∧
      (∀ upper lower first second,
        source.coordinateCurvatureAt point upper lower first second =
          -source.coordinateCurvatureAt point upper lower second first) := by
  exact
    ⟨source.coframeAt_contDiff, source.metricAt_contDiff, point.2,
      rfl, rfl, (source.geometryAt point).spin.affineTorsionFree,
      (source.geometryAt point).spin.tetradCompatible, rfl,
      source.coordinateCurvatureAt_antisymm point⟩

/-! ## Exact affine-metric two-jet and curvature at the source origin -/

namespace Source

def metricFirstDerivativeAtOrigin
    (source : Source)
    (direction first second : LorentzianIndex) : ℝ :=
  (source.jetAt 0).metricDerivative direction first second

/-- Exact second derivative of `eᵀ η e` for the affine coframe grammar.
The coframe has zero second derivative, so only the two product-rule cross
terms remain. -/
def metricSecondDerivativeAtOrigin
    (source : Source)
    (firstDirection secondDirection first second : LorentzianIndex) : ℝ :=
  ∑ internal, minkowskiInternalSign internal *
    (source.coframeLinearCoefficient firstDirection internal first *
        source.coframeLinearCoefficient secondDirection internal second +
      source.coframeLinearCoefficient secondDirection internal first *
        source.coframeLinearCoefficient firstDirection internal second)

def loweredChristoffelAtOrigin
    (source : Source)
    (loweredIndex direction first : LorentzianIndex) : ℝ :=
  (source.jetAt 0).loweredLeviCivitaConnection loweredIndex direction first

def raisedChristoffelAtOrigin
    (source : Source)
    (upper direction lower : LorentzianIndex) : ℝ :=
  minkowskiInternalSign upper *
    source.loweredChristoffelAtOrigin upper direction lower

/-- `∂_κ g^{ρλ} = -g^{ρα}(∂_κ g_{αβ})g^{βλ}` at the identity
coframe origin. -/
def inverseMetricDerivativeAtOrigin
    (source : Source)
    (direction first second : LorentzianIndex) : ℝ :=
  -(minkowskiInternalSign first * minkowskiInternalSign second *
    source.metricFirstDerivativeAtOrigin direction first second)

def loweredChristoffelDerivativeAtOrigin
    (source : Source)
    (derivativeDirection loweredIndex first second : LorentzianIndex) : ℝ :=
  (source.metricSecondDerivativeAtOrigin derivativeDirection first
        second loweredIndex +
      source.metricSecondDerivativeAtOrigin derivativeDirection second
        first loweredIndex -
      source.metricSecondDerivativeAtOrigin derivativeDirection loweredIndex
        first second) / 2

def raisedChristoffelDerivativeAtOrigin
    (source : Source)
    (derivativeDirection upper first second : LorentzianIndex) : ℝ :=
  ∑ loweredIndex, (
    source.inverseMetricDerivativeAtOrigin derivativeDirection upper loweredIndex *
        source.loweredChristoffelAtOrigin loweredIndex first second +
      (if upper = loweredIndex then minkowskiInternalSign upper else 0) *
        source.loweredChristoffelDerivativeAtOrigin derivativeDirection
          loweredIndex first second)

/-- Exact coordinate Riemann-curvature expression at the source origin. -/
def coordinateCurvatureAtOrigin
    (source : Source)
    (upper lower first second : LorentzianIndex) : ℝ :=
  source.raisedChristoffelDerivativeAtOrigin first upper second lower -
      source.raisedChristoffelDerivativeAtOrigin second upper first lower +
    ∑ middle,
      (source.raisedChristoffelAtOrigin upper first middle *
          source.raisedChristoffelAtOrigin middle second lower -
        source.raisedChristoffelAtOrigin upper second middle *
          source.raisedChristoffelAtOrigin middle first lower)

theorem coordinateCurvatureAtOrigin_antisymm
    (source : Source) (upper lower first second : LorentzianIndex) :
    source.coordinateCurvatureAtOrigin upper lower first second =
      -source.coordinateCurvatureAtOrigin upper lower second first := by
  unfold coordinateCurvatureAtOrigin
  have hsum :
      (∑ middle,
        (source.raisedChristoffelAtOrigin upper first middle *
            source.raisedChristoffelAtOrigin middle second lower -
          source.raisedChristoffelAtOrigin upper second middle *
            source.raisedChristoffelAtOrigin middle first lower)) =
        -∑ middle,
          (source.raisedChristoffelAtOrigin upper second middle *
              source.raisedChristoffelAtOrigin middle first lower -
            source.raisedChristoffelAtOrigin upper first middle *
              source.raisedChristoffelAtOrigin middle second lower) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro middle _
    ring
  rw [hsum]
  ring

/-- Lorentz-curvature two-form at the identity-frame origin, with its first
internal index lowered by the Minkowski sign. -/
def lorentzCurvatureAtOrigin (source : Source) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    minkowskiInternalSign (pairFirst internalPair) *
      source.coordinateCurvatureAtOrigin
        (pairFirst internalPair) (pairSecond internalPair)
        (pairFirst spacetimePair) (pairSecond spacetimePair)

end Source

/-- Full generated origin geometry.  Every field is computed from `Source`;
the source itself contains none of these outputs or laws. -/
structure GeneratedOriginGeometry (source : Source) where
  jet : PointwiseLorentzianCoframeJet
  jet_eq : jet = source.jetAt 0
  coframeNondegenerate : Matrix.det jet.coframe ≠ 0
  pointwiseGeometry : PointwiseLorentzGeometryOutput jet
  physicalBivector : PhysicalBivector
  physicalBivector_eq :
    physicalBivector = physicalIIPlusBivector jet.coframe
  lorentzCurvature : PhysicalBivector
  lorentzCurvature_eq :
    lorentzCurvature = source.lorentzCurvatureAtOrigin

def generatedOriginGeometry (source : Source) :
    GeneratedOriginGeometry source where
  jet := source.jetAt 0
  jet_eq := rfl
  coframeNondegenerate := source.jetAt_zero_nondegenerate
  pointwiseGeometry := source.geometryAtOrigin
  physicalBivector := physicalIIPlusBivector (source.jetAt 0).coframe
  physicalBivector_eq := rfl
  lorentzCurvature := source.lorentzCurvatureAtOrigin
  lorentzCurvature_eq := rfl

/-- The positive shear source has genuinely nonzero generated curvature; the
curvature producer is not an all-zero readout. -/
theorem positiveSource_curvature_nonzero_component :
    positiveSource.coordinateCurvatureAtOrigin 0 1 0 1 = -(1 / 4 : ℝ) := by
  simp [Source.coordinateCurvatureAtOrigin,
    Source.raisedChristoffelDerivativeAtOrigin,
    Source.inverseMetricDerivativeAtOrigin,
    Source.metricFirstDerivativeAtOrigin,
    Source.loweredChristoffelDerivativeAtOrigin,
    Source.metricSecondDerivativeAtOrigin,
    Source.raisedChristoffelAtOrigin,
    Source.loweredChristoffelAtOrigin,
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection,
    PointwiseLorentzianCoframeJet.metricDerivative,
    Source.jetAt, positiveSource, shearCoefficient,
    minkowskiInternalSign, Fin.sum_univ_four]
  all_goals norm_num

theorem proofFreeSource_generates_origin_geometry (source : Source) :
    let output := generatedOriginGeometry source
    output.jet = source.jetAt 0 ∧
      Matrix.det output.jet.coframe ≠ 0 ∧
      output.physicalBivector = physicalIIPlusBivector output.jet.coframe ∧
      output.lorentzCurvature = source.lorentzCurvatureAtOrigin := by
  exact ⟨rfl, source.jetAt_zero_nondegenerate, rfl, rfl⟩

end
end SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource
