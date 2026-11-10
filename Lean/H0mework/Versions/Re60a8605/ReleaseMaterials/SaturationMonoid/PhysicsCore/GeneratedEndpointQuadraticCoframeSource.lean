import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.PhysicalSourcePullback
import H0mework.Physics.Lorentz.PointwiseLorentzGeometryOutput
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.SU7GeneratedCenterCoverPath

/-!
# Generated-endpoint / quadratic-coordinate coframe source

This module closes a narrow positive source-to-coframe mouth without claiming
that the discrete SU(7) endpoint axis determines spacetime geometry.

The smooth-geometry axis is a family of separable quadratic coordinate
potentials.  Its raw fields are polynomial coefficients and an endpoint
anchor; it stores no coframe jet, metric, Hodge operator, affine/spin
connection, gluing certificate, or final admissibility proposition.  The
coframe is computed as the first-order Taylor coefficient (Jacobian) of the
potentials, and its first derivative is computed from the quadratic
coefficients.  Exact Taylor identities verify both readouts.

The geometry observation is paired with a genuinely generated endpoint pair
using the existing equal-anchor `SharedPhysicalSource`.  On the native
nondegenerate slice, the resulting jet feeds the existing metric/Hodge,
Levi-Civita, Lorentz-spin, and two-chart omega-gluing producers.

Boundary: this is a concrete global polynomial-coordinate geometry axis and a
pointwise output theorem.  It is an exact-coframe/coordinate-pullback slice,
not a general anholonomic tetrad, curved source-generated field, nonconstant
principal transition, curvature theorem, stationary Plebanski family, or a
proof that the endpoint grammar selects the geometry coefficients.
-/

namespace SaturationMonoid
namespace PhysicsCore
namespace GeneratedEndpointQuadraticCoframeSource

open scoped Matrix
open SU7GeneratedCenterCoverPath

noncomputable section

abbrev LorentzianCoordinatePoint := LorentzianIndex → ℝ

/-- Independent smooth-geometry source coordinates.  `linearCoefficient` and
`quadraticCoefficient` are coefficients of scalar coordinate potentials, not
reported tetrads or connections. -/
structure QuadraticCoordinateSource where
  endpointAnchor : Nat × Nat
  offset : LorentzianIndex → ℝ
  linearCoefficient : LorentzianCoframe
  quadraticCoefficient : LorentzianCoframe

namespace QuadraticCoordinateSource

/-- Four separable quadratic coordinate potentials, one for each internal
index. -/
def coordinatePotential
    (S : QuadraticCoordinateSource)
    (point : LorentzianCoordinatePoint)
    (internal : LorentzianIndex) : ℝ :=
  S.offset internal +
    ∑ coordinate : LorentzianIndex,
      (S.linearCoefficient internal coordinate * point coordinate +
        S.quadraticCoefficient internal coordinate *
          (point coordinate) ^ 2 / 2)

/-- Jacobian coframe computed from the first-order coefficient of the
quadratic coordinate potentials. -/
def coframeAt
    (S : QuadraticCoordinateSource)
    (point : LorentzianCoordinatePoint) : LorentzianCoframe :=
  fun internal coordinate =>
    S.linearCoefficient internal coordinate +
      S.quadraticCoefficient internal coordinate * point coordinate

/-- Exact first derivative of the computed coframe.  The separable source has
only the matching direction/coordinate Hessian component. -/
def coframeDerivative
    (S : QuadraticCoordinateSource) : LorentzianCoframeDerivative :=
  fun direction internal coordinate =>
    if direction = coordinate then
      S.quadraticCoefficient internal coordinate
    else 0

def coframeIncrement
    (S : QuadraticCoordinateSource)
    (displacement : LorentzianCoordinatePoint) : LorentzianCoframe :=
  fun internal coordinate =>
    S.quadraticCoefficient internal coordinate * displacement coordinate

/-- Exact second-order Taylor law.  The computed coframe is precisely the
linear coefficient of the coordinate-potential increment; no target coframe
is supplied as a premise. -/
theorem coordinatePotential_add
    (S : QuadraticCoordinateSource)
    (point displacement : LorentzianCoordinatePoint)
    (internal : LorentzianIndex) :
    S.coordinatePotential (point + displacement) internal =
      S.coordinatePotential point internal +
        ∑ coordinate : LorentzianIndex,
          (S.coframeAt point internal coordinate *
              displacement coordinate +
            S.quadraticCoefficient internal coordinate *
              (displacement coordinate) ^ 2 / 2) := by
  unfold coordinatePotential coframeAt
  calc
    S.offset internal +
          ∑ coordinate : LorentzianIndex,
            (S.linearCoefficient internal coordinate *
                  (point + displacement) coordinate +
              S.quadraticCoefficient internal coordinate *
                  ((point + displacement) coordinate) ^ 2 / 2) =
        S.offset internal +
          ∑ coordinate : LorentzianIndex,
            ((S.linearCoefficient internal coordinate * point coordinate +
                S.quadraticCoefficient internal coordinate *
                  (point coordinate) ^ 2 / 2) +
              ((S.linearCoefficient internal coordinate +
                    S.quadraticCoefficient internal coordinate *
                      point coordinate) * displacement coordinate +
                S.quadraticCoefficient internal coordinate *
                  (displacement coordinate) ^ 2 / 2)) := by
      apply congrArg (fun value => S.offset internal + value)
      apply Finset.sum_congr rfl
      intro coordinate _hcoordinate
      simp only [Pi.add_apply]
      ring
    _ =
        (S.offset internal +
            ∑ coordinate : LorentzianIndex,
              (S.linearCoefficient internal coordinate * point coordinate +
                S.quadraticCoefficient internal coordinate *
                  (point coordinate) ^ 2 / 2)) +
          ∑ coordinate : LorentzianIndex,
            ((S.linearCoefficient internal coordinate +
                  S.quadraticCoefficient internal coordinate *
                    point coordinate) * displacement coordinate +
              S.quadraticCoefficient internal coordinate *
                (displacement coordinate) ^ 2 / 2) := by
      rw [Finset.sum_add_distrib]
      ring

/-- Exact affine increment law for the Jacobian coframe. -/
theorem coframeAt_add
    (S : QuadraticCoordinateSource)
    (point displacement : LorentzianCoordinatePoint) :
    S.coframeAt (point + displacement) =
      S.coframeAt point + S.coframeIncrement displacement := by
  ext internal coordinate
  simp only [coframeAt, coframeIncrement, Pi.add_apply, Matrix.add_apply]
  ring

/-- Contracting the generated three-index derivative with a displacement
recovers the exact coframe increment. -/
theorem coframeDerivative_contract
    (S : QuadraticCoordinateSource)
    (displacement : LorentzianCoordinatePoint)
    (internal coordinate : LorentzianIndex) :
    ∑ direction : LorentzianIndex,
        S.coframeDerivative direction internal coordinate *
          displacement direction =
      S.quadraticCoefficient internal coordinate *
        displacement coordinate := by
  simp [coframeDerivative]

/-- Pointwise coframe first jet generated from the polynomial source. -/
def jetAt
    (S : QuadraticCoordinateSource)
    (point : LorentzianCoordinatePoint) :
    PointwiseLorentzianCoframeJet where
  coframe := S.coframeAt point
  derivative := S.coframeDerivative

@[simp] theorem jetAt_coframe
    (S : QuadraticCoordinateSource)
    (point : LorentzianCoordinatePoint) :
    (S.jetAt point).coframe = S.coframeAt point :=
  rfl

@[simp] theorem jetAt_derivative
    (S : QuadraticCoordinateSource)
    (point : LorentzianCoordinatePoint) :
    (S.jetAt point).derivative = S.coframeDerivative :=
  rfl

end QuadraticCoordinateSource

/-- A source field observed at one coordinate point. -/
structure GeometryObservation where
  source : QuadraticCoordinateSource
  point : LorentzianCoordinatePoint

namespace GeometryObservation

def endpointAnchor (observation : GeometryObservation) : Nat × Nat :=
  observation.source.endpointAnchor

def generatedJet
    (observation : GeometryObservation) :
    PointwiseLorentzianCoframeJet :=
  observation.source.jetAt observation.point

end GeometryObservation

/-- Genuinely generated finite endpoint pairs used as the discrete source
axis. -/
abbrev GeneratedEndpointSource (n bound : Nat) :=
  { pair : Nat × Nat // GeneratedEndpointPair n bound pair }

/-- Richer two-axis source: a generated endpoint and a polynomial geometry
observation are paired by exact endpoint-anchor equality, not an arbitrary
downstream compatibility predicate. -/
abbrev SharedGeneratedQuadraticSource (n bound : Nat) :=
  SharedPhysicalSource
    (GeneratedEndpointSource n bound) GeometryObservation (Nat × Nat)
    (fun endpoint => endpoint.1) GeometryObservation.endpointAnchor

namespace SharedGeneratedQuadraticSource

variable {n bound : Nat}

def endpointPair
    (source : SharedGeneratedQuadraticSource n bound) : Nat × Nat :=
  source.1.1.1

def geometryObservation
    (source : SharedGeneratedQuadraticSource n bound) : GeometryObservation :=
  source.1.2

def generatedJet
    (source : SharedGeneratedQuadraticSource n bound) :
    PointwiseLorentzianCoframeJet :=
  source.geometryObservation.generatedJet

theorem endpointPair_generated
    (source : SharedGeneratedQuadraticSource n bound) :
    GeneratedEndpointPair n bound source.endpointPair :=
  source.1.1.2

theorem endpointAnchor_eq
    (source : SharedGeneratedQuadraticSource n bound) :
    source.endpointPair = source.geometryObservation.endpointAnchor :=
  source.2

def endpointProjection
    (source : SharedGeneratedQuadraticSource n bound) :
    GeneratedEndpointSource n bound :=
  source.1.1

end SharedGeneratedQuadraticSource

/-! ## Produced pointwise geometry -/

/-- Source-specific producer theorem.  Its only premise is the native
nondegeneracy of the computed Jacobian coframe; no target geometry object or
compatibility/final-admissibility certificate is accepted. -/
def SharedGeneratedQuadraticSource.producePointwiseLorentzGeometry
    {n bound : Nat}
    (source : SharedGeneratedQuadraticSource n bound)
    (hcoframe : Matrix.det source.generatedJet.coframe ≠ 0) :
    PointwiseLorentzGeometryOutput source.generatedJet :=
  producePointwiseLorentzGeometryFromJet source.generatedJet hcoframe

/-! ## Nonconstant positive model at a generated endpoint -/

/-- Flat identity-coordinate source used only to prove that the discrete
endpoint projection does not determine the independent geometry axis. -/
def flatCoordinateSource
    (anchor : Nat × Nat) : QuadraticCoordinateSource where
  endpointAnchor := anchor
  offset := 0
  linearCoefficient := 1
  quadraticCoefficient := 0

@[simp] theorem flatCoordinateSource_jet_derivative
    (anchor : Nat × Nat) :
    ((flatCoordinateSource anchor).jetAt 0).derivative = 0 := by
  funext direction internal coordinate
  simp [QuadraticCoordinateSource.jetAt,
    QuadraticCoordinateSource.coframeDerivative,
    flatCoordinateSource]

/-- A single nonzero quadratic coefficient in the time potential. -/
def timeQuadraticCoefficient : LorentzianCoframe :=
  fun internal coordinate =>
    if internal = 0 ∧ coordinate = 0 then 1 else 0

/-- Nonconstant quadratic coordinate source with identity Jacobian at the
origin. -/
def nonconstantCoordinateSource
    (anchor : Nat × Nat) : QuadraticCoordinateSource where
  endpointAnchor := anchor
  offset := 0
  linearCoefficient := 1
  quadraticCoefficient := timeQuadraticCoefficient

theorem nonconstantCoordinateSource_coframeAt_zero
    (anchor : Nat × Nat) :
    (nonconstantCoordinateSource anchor).coframeAt 0 = 1 := by
  ext internal coordinate
  simp [QuadraticCoordinateSource.coframeAt,
    nonconstantCoordinateSource]

@[simp] theorem nonconstantCoordinateSource_timeDerivative
    (anchor : Nat × Nat) :
    ((nonconstantCoordinateSource anchor).jetAt 0).derivative 0 0 0 = 1 := by
  simp [QuadraticCoordinateSource.jetAt,
    QuadraticCoordinateSource.coframeDerivative,
    nonconstantCoordinateSource, timeQuadraticCoefficient]

theorem nonconstantCoordinateSource_derivative_ne_zero
    (anchor : Nat × Nat) :
    ((nonconstantCoordinateSource anchor).jetAt 0).derivative ≠ 0 := by
  intro hzero
  have hcomponent := congrFun (congrFun (congrFun hzero 0) 0) 0
  simp at hcomponent

theorem nonconstantCoordinateSource_nondegenerate
    (anchor : Nat × Nat) :
    Matrix.det ((nonconstantCoordinateSource anchor).jetAt 0).coframe ≠ 0 := by
  rw [QuadraticCoordinateSource.jetAt_coframe,
    nonconstantCoordinateSource_coframeAt_zero]
  simp

def generatedThreeThreeEndpoint : GeneratedEndpointSource 3 3 :=
  ⟨(3, 3), pair_three_three_three_three⟩

def flatThreeThreeObservation : GeometryObservation where
  source := flatCoordinateSource (3, 3)
  point := 0

def flatThreeThreeSharedSource :
    SharedGeneratedQuadraticSource 3 3 :=
  ⟨(generatedThreeThreeEndpoint, flatThreeThreeObservation), rfl⟩

def nonconstantThreeThreeObservation : GeometryObservation where
  source := nonconstantCoordinateSource (3, 3)
  point := 0

/-- Concrete equal-anchor richer source.  The generated endpoint and geometry
axis are both retained; neither is reconstructed from the other. -/
def nonconstantThreeThreeSharedSource :
    SharedGeneratedQuadraticSource 3 3 :=
  ⟨(generatedThreeThreeEndpoint, nonconstantThreeThreeObservation), rfl⟩

@[simp] theorem nonconstantThreeThreeSharedSource_endpointPair :
    nonconstantThreeThreeSharedSource.endpointPair = (3, 3) :=
  rfl

theorem nonconstantThreeThreeSharedSource_jet_derivative_ne_zero :
    nonconstantThreeThreeSharedSource.generatedJet.derivative ≠ 0 :=
  nonconstantCoordinateSource_derivative_ne_zero (3, 3)

theorem flatThreeThreeSharedSource_jet_derivative_zero :
    flatThreeThreeSharedSource.generatedJet.derivative = 0 :=
  flatCoordinateSource_jet_derivative (3, 3)

theorem threeThree_generatedJets_distinct :
    flatThreeThreeSharedSource.generatedJet ≠
      nonconstantThreeThreeSharedSource.generatedJet := by
  intro hequal
  have hderivative := congrArg PointwiseLorentzianCoframeJet.derivative hequal
  apply nonconstantThreeThreeSharedSource_jet_derivative_ne_zero
  rw [← hderivative]
  exact flatThreeThreeSharedSource_jet_derivative_zero

theorem threeThree_sharedSources_distinct :
    flatThreeThreeSharedSource ≠
      nonconstantThreeThreeSharedSource := by
  intro hequal
  exact threeThree_generatedJets_distinct
    (congrArg SharedGeneratedQuadraticSource.generatedJet hequal)

/-- The discrete generated endpoint projection is not a geometry selector:
the same endpoint pair supports distinct independently sourced coframe jets. -/
theorem threeThree_endpointProjection_not_injective :
    ¬ Function.Injective
        (SharedGeneratedQuadraticSource.endpointProjection
          (n := 3) (bound := 3)) := by
  intro hinjective
  apply threeThree_sharedSources_distinct
  apply hinjective
  rfl

theorem nonconstantThreeThreeSharedSource_nondegenerate :
    Matrix.det nonconstantThreeThreeSharedSource.generatedJet.coframe ≠ 0 :=
  nonconstantCoordinateSource_nondegenerate (3, 3)

/-- A genuinely generated endpoint paired with a nonconstant polynomial
geometry axis produces the full existing pointwise Lorentz geometry output. -/
def nonconstantThreeThreePointwiseLorentzGeometry :
    PointwiseLorentzGeometryOutput
      nonconstantThreeThreeSharedSource.generatedJet :=
  nonconstantThreeThreeSharedSource.producePointwiseLorentzGeometry
    nonconstantThreeThreeSharedSource_nondegenerate

theorem generatedEndpoint_and_nonconstantGeometry_produce_pointwiseLorentz :
    GeneratedEndpointPair 3 3
        nonconstantThreeThreeSharedSource.endpointPair ∧
      nonconstantThreeThreeSharedSource.generatedJet.derivative ≠ 0 ∧
        Nonempty
          (PointwiseLorentzGeometryOutput
            nonconstantThreeThreeSharedSource.generatedJet) :=
  ⟨nonconstantThreeThreeSharedSource.endpointPair_generated,
    nonconstantThreeThreeSharedSource_jet_derivative_ne_zero,
    ⟨nonconstantThreeThreePointwiseLorentzGeometry⟩⟩

end
end GeneratedEndpointQuadraticCoframeSource
end PhysicsCore
end SaturationMonoid
