import H0mework.Physics.Source.PhysicalIIPlusNativeVariation
import H0mework.Physics.Lorentz.LorentzConnectionVariation

/-!
# Formulation-neutral II+ torsion reduction

This module supplies a finite-coordinate kinematic seam used to compare
candidate Stage-9 gravity formulations.  It does **not** choose or freeze a
root action, and it neither assumes nor produces a shell equation,
stationarity, a solution, source data, or a fixed actual.

`PhysicalBivector` carries the standard contravariant `Lambda^2` action.  The
internal Hodge transport

`undual -> ordinary bivector action -> dual`

is kept as a separate comparison map.  Lean proves that the two actions agree
on the explicit `LorentzSkew` domain; the transport is not used to define the
authoritative covariant derivative.

For an arbitrary pointwise coframe first jet and a Lorentz-skew pointwise
connection, the module then proves

`D_omega II+(e) = star_internal (T(omega,e) wedge e)`

as an equality of typed bivector-valued three-form coordinates.  This is only
the object-level Cartan reduction identity needed by the later A/B
formulation-jurisdiction audit.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineResidualLinearPlebanskiTorsionReduction

open ProofFreeRicherAnholonomicSource
open PointwiseDiracSpinConnectionLift
open StageNineCartanTangentSimplicityResponse
open StageNineLorentzConnectionVariation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

/-! ## Typed pointwise bivector connection -/

/-- The inverse internal dual on the physical bivector carrier.  The fixed
Lorentzian internal Hodge squares to `-1`, so its inverse is `-star`. -/
def internalBivectorUndual (bivector : PhysicalBivector) : PhysicalBivector :=
  -internalBivectorDual bivector

theorem internalBivectorUndual_dual
    (bivector : PhysicalBivector) :
    internalBivectorUndual (internalBivectorDual bivector) = bivector := by
  funext internalPair spacetimePair
  fin_cases internalPair <;>
    simp [internalBivectorUndual, internalBivectorDual,
      lorentzianCoframeHodge]

theorem internalBivectorDual_undual
    (bivector : PhysicalBivector) :
    internalBivectorDual (internalBivectorUndual bivector) = bivector := by
  funext internalPair spacetimePair
  fin_cases internalPair <;>
    simp [internalBivectorUndual, internalBivectorDual,
      lorentzianCoframeHodge]

/-- Recover an ordered internal two-form component from the six canonical
pair coordinates. -/
def orderedInternalBivectorComponent
    (bivector : PhysicalBivector)
    (first second : LorentzianIndex)
    (spacetimePair : Fin 6) : ℝ :=
  ∑ internalPair : Fin 6,
    bivector internalPair spacetimePair *
      orientedLorentzBivectorBasisCoefficient internalPair first second

/-- Standard contravariant `Lambda^2` connection action on internal
bivector coordinates. -/
def ordinaryLorentzBivectorConnectionAction
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex)
    (bivector : PhysicalBivector) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    (∑ middle : LorentzianIndex,
      connection direction (pairFirst internalPair) middle *
        orderedInternalBivectorComponent bivector middle
          (pairSecond internalPair) spacetimePair) +
    ∑ middle : LorentzianIndex,
      connection direction (pairSecond internalPair) middle *
        orderedInternalBivectorComponent bivector
          (pairFirst internalPair) middle spacetimePair

/-- Hodge-transported comparison action.  This is deliberately not the
authoritative `D_omega` action; it agrees with the standard action only after
the Lorentz-skew domain gate is proved. -/
def dualTransportedLorentzBivectorConnectionAction
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex)
    (bivector : PhysicalBivector) : PhysicalBivector :=
  internalBivectorDual
    (ordinaryLorentzBivectorConnectionAction connection direction
      (internalBivectorUndual bivector))

/-- Internal Hodge equivariance of the standard bivector representation on
the Lorentz-skew domain. -/
theorem ordinaryConnectionAction_internalBivectorDual
    (connection : PointwiseLorentzSpinConnection)
    (connectionSkew : LorentzSkew connection)
    (direction : LorentzianIndex)
    (bivector : PhysicalBivector) :
    ordinaryLorentzBivectorConnectionAction connection direction
        (internalBivectorDual bivector) =
      internalBivectorDual
        (ordinaryLorentzBivectorConnectionAction connection direction
          bivector) := by
  have h00 := lorentzSkew_diagonal_zero connection connectionSkew direction 0
  have h11 := lorentzSkew_diagonal_zero connection connectionSkew direction 1
  have h22 := lorentzSkew_diagonal_zero connection connectionSkew direction 2
  have h33 := lorentzSkew_diagonal_zero connection connectionSkew direction 3
  have h10 : connection direction 1 0 = connection direction 0 1 := by
    have h := lorentzSkew_entry connection connectionSkew direction 0 1
    simp only [minkowskiInternalSign_one_value,
      minkowskiInternalSign_zero_value, one_mul, neg_one_mul] at h
    linarith
  have h20 : connection direction 2 0 = connection direction 0 2 := by
    have h := lorentzSkew_entry connection connectionSkew direction 0 2
    simp only [minkowskiInternalSign_two_value,
      minkowskiInternalSign_zero_value, one_mul, neg_one_mul] at h
    linarith
  have h30 : connection direction 3 0 = connection direction 0 3 := by
    have h := lorentzSkew_entry connection connectionSkew direction 0 3
    simp only [minkowskiInternalSign_three_value,
      minkowskiInternalSign_zero_value, one_mul, neg_one_mul] at h
    linarith
  have h21 : connection direction 2 1 = -connection direction 1 2 := by
    have h := lorentzSkew_entry connection connectionSkew direction 1 2
    simp only [minkowskiInternalSign_two_value,
      minkowskiInternalSign_one_value, one_mul] at h
    linarith
  have h31 : connection direction 3 1 = -connection direction 1 3 := by
    have h := lorentzSkew_entry connection connectionSkew direction 1 3
    simp only [minkowskiInternalSign_three_value,
      minkowskiInternalSign_one_value, one_mul] at h
    linarith
  have h32 : connection direction 3 2 = -connection direction 2 3 := by
    have h := lorentzSkew_entry connection connectionSkew direction 2 3
    simp only [minkowskiInternalSign_three_value,
      minkowskiInternalSign_two_value, one_mul] at h
    linarith
  funext internalPair spacetimePair
  fin_cases internalPair <;>
    simp [ordinaryLorentzBivectorConnectionAction,
      orderedInternalBivectorComponent,
      orientedLorentzBivectorBasisCoefficient,
      internalBivectorDual, lorentzianCoframeHodge,
      pairFirst, pairSecond, Fin.sum_univ_four, Fin.sum_univ_six] <;>
    simp only [h00, h11, h22, h33, h10, h20, h30, h21, h31, h32] <;>
    ring

/-- Representation-authority seam: on `so(1,3)`, the standard
contravariant action equals the separately defined Hodge transport. -/
theorem ordinaryConnectionAction_eq_dualTransported
    (connection : PointwiseLorentzSpinConnection)
    (connectionSkew : LorentzSkew connection)
    (direction : LorentzianIndex)
    (bivector : PhysicalBivector) :
    ordinaryLorentzBivectorConnectionAction connection direction bivector =
      dualTransportedLorentzBivectorConnectionAction connection direction
        bivector := by
  calc
    ordinaryLorentzBivectorConnectionAction connection direction bivector =
        ordinaryLorentzBivectorConnectionAction connection direction
          (internalBivectorDual (internalBivectorUndual bivector)) := by
            rw [internalBivectorDual_undual]
    _ = internalBivectorDual
          (ordinaryLorentzBivectorConnectionAction connection direction
            (internalBivectorUndual bivector)) :=
      ordinaryConnectionAction_internalBivectorDual connection connectionSkew
        direction (internalBivectorUndual bivector)
    _ = dualTransportedLorentzBivectorConnectionAction connection direction
          bivector := rfl

/-- A value and its four coordinate derivatives at one point. -/
structure PointwisePhysicalBivectorJet where
  value : PhysicalBivector
  derivative : LorentzianIndex → PhysicalBivector

/-- Typed pointwise covariant derivative `nabla_direction B`. -/
def pointwisePhysicalBivectorCovariantDerivative
    (connection : PointwiseLorentzSpinConnection)
    (jet : PointwisePhysicalBivectorJet)
    (direction : LorentzianIndex) : PhysicalBivector :=
  jet.derivative direction +
    ordinaryLorentzBivectorConnectionAction connection direction jet.value

/-! ## Coframe jet, torsion, and the II+ derivative -/

/-- The connection contribution `omega_direction e` to a coframe
derivative. -/
def coframeConnectionAction
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex)
    (coframe : LorentzianCoframe) : LorentzianCoframe :=
  fun internal coordinate =>
    ∑ middle : LorentzianIndex,
      connection direction internal middle * coframe middle coordinate

/-- Pointwise coframe covariant derivative. -/
def pointwiseCoframeCovariantDerivative
    (jet : PointwiseLorentzianCoframeJet)
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex) : LorentzianCoframe :=
  fun internal coordinate =>
    jet.derivative direction internal coordinate +
      coframeConnectionAction connection direction jet.coframe
        internal coordinate

/-- Cartan torsion obtained from the antisymmetrized coframe covariant
derivative.  The argument order is `(first, second, internal)`. -/
def pointwiseCartanTorsion
    (jet : PointwiseLorentzianCoframeJet)
    (connection : PointwiseLorentzSpinConnection)
    (first second internal : LorentzianIndex) : ℝ :=
  pointwiseCoframeCovariantDerivative jet connection first internal second -
    pointwiseCoframeCovariantDerivative jet connection second internal first

/-- The pointwise first jet of `II+(e)` generated by the coframe first jet. -/
def pointwisePhysicalIIPlusJet
    (jet : PointwiseLorentzianCoframeJet) :
    PointwisePhysicalBivectorJet where
  value := physicalIIPlusBivector jet.coframe
  derivative := fun direction =>
    physicalIIPlusCoframeTangent jet.coframe
      (fun internal coordinate => jet.derivative direction internal coordinate)

theorem coframeWedgeTangent_add
    (coframe first second : LorentzianCoframe) :
    coframeWedgeTangent coframe (first + second) =
      coframeWedgeTangent coframe first +
        coframeWedgeTangent coframe second := by
  funext internalPair spacetimePair
  simp [coframeWedgeTangent]
  ring

theorem physicalIIPlusCoframeTangent_add
    (coframe first second : LorentzianCoframe) :
    physicalIIPlusCoframeTangent coframe (first + second) =
      physicalIIPlusCoframeTangent coframe first +
        physicalIIPlusCoframeTangent coframe second := by
  unfold physicalIIPlusCoframeTangent
  rw [coframeWedgeTangent_add]
  funext internalPair spacetimePair
  fin_cases internalPair <;>
    simp [internalBivectorDual, lorentzianCoframeHodge] <;>
    abel

theorem ordinaryConnectionAction_coframeWedge
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex)
    (coframe : LorentzianCoframe) :
    ordinaryLorentzBivectorConnectionAction connection direction
        (coframeWedge coframe) =
      coframeWedgeTangent coframe
        (coframeConnectionAction connection direction coframe) := by
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [ordinaryLorentzBivectorConnectionAction,
      orderedInternalBivectorComponent,
      orientedLorentzBivectorBasisCoefficient,
      coframeConnectionAction, coframeWedge, coframeWedgeTangent,
      pairFirst, pairSecond, Fin.sum_univ_four, Fin.sum_univ_six] <;>
    ring

/-- The Hodge-transported comparison action on `II+(e)` is definitionally
the native `II+` tangent in the connection-generated coframe direction. -/
theorem dualTransportedConnectionAction_physicalIIPlus
    (connection : PointwiseLorentzSpinConnection)
    (direction : LorentzianIndex)
    (coframe : LorentzianCoframe) :
    dualTransportedLorentzBivectorConnectionAction connection direction
        (physicalIIPlusBivector coframe) =
      physicalIIPlusCoframeTangent coframe
        (coframeConnectionAction connection direction coframe) := by
  unfold dualTransportedLorentzBivectorConnectionAction
  rw [show physicalIIPlusBivector coframe =
      internalBivectorDual (coframeWedge coframe) by rfl]
  rw [internalBivectorUndual_dual]
  rw [ordinaryConnectionAction_coframeWedge]
  rfl

/-- The authoritative standard `Lambda^2` action has the expected `II+`
tangent only on the explicit Lorentz-skew domain. -/
theorem ordinaryConnectionAction_physicalIIPlus
    (connection : PointwiseLorentzSpinConnection)
    (connectionSkew : LorentzSkew connection)
    (direction : LorentzianIndex)
    (coframe : LorentzianCoframe) :
    ordinaryLorentzBivectorConnectionAction connection direction
        (physicalIIPlusBivector coframe) =
      physicalIIPlusCoframeTangent coframe
        (coframeConnectionAction connection direction coframe) := by
  rw [ordinaryConnectionAction_eq_dualTransported connection connectionSkew]
  exact dualTransportedConnectionAction_physicalIIPlus connection direction
    coframe

/-- Directional covariant differentiation commutes with the physical `II+`
substitution at the pointwise-jet level. -/
theorem pointwisePhysicalIIPlus_covariantDerivative
    (jet : PointwiseLorentzianCoframeJet)
    (connection : PointwiseLorentzSpinConnection)
    (connectionSkew : LorentzSkew connection)
    (direction : LorentzianIndex) :
    pointwisePhysicalBivectorCovariantDerivative connection
        (pointwisePhysicalIIPlusJet jet) direction =
      physicalIIPlusCoframeTangent jet.coframe
        (pointwiseCoframeCovariantDerivative jet connection direction) := by
  unfold pointwisePhysicalBivectorCovariantDerivative
  simp only [pointwisePhysicalIIPlusJet]
  rw [ordinaryConnectionAction_physicalIIPlus connection connectionSkew]
  funext internalPair spacetimePair
  fin_cases internalPair <;>
    simp [pointwiseCoframeCovariantDerivative,
      physicalIIPlusCoframeTangent, internalBivectorDual,
      coframeWedgeTangent, lorentzianCoframeHodge] <;>
    ring

/-! ## Exterior covariant derivative and torsion--coframe identity -/

/-- Canonical oriented three-form order `(012, 013, 023, 123)`. -/
def threeFormFirst : Fin 4 → LorentzianIndex := ![0, 0, 0, 1]

def threeFormSecond : Fin 4 → LorentzianIndex := ![1, 1, 2, 2]

def threeFormThird : Fin 4 → LorentzianIndex := ![2, 3, 3, 3]

/-- Bivector-valued three-form coordinates: six internal pairs and four
oriented spacetime triples. -/
abbrev PhysicalBivectorThreeForm := Fin 6 → Fin 4 → ℝ

/-- Recover an ordered spacetime two-form component from canonical pair
coordinates. -/
def orderedSpacetimeBivectorComponent
    (bivector : PhysicalBivector)
    (internalPair : Fin 6)
    (first second : LorentzianIndex) : ℝ :=
  ∑ spacetimePair : Fin 6,
    bivector internalPair spacetimePair *
      orientedLorentzBivectorBasisCoefficient spacetimePair first second

/-- Typed exterior covariant derivative `D_omega B`. -/
def pointwisePhysicalBivectorExteriorCovariantDerivative
    (connection : PointwiseLorentzSpinConnection)
    (jet : PointwisePhysicalBivectorJet) : PhysicalBivectorThreeForm :=
  fun internalPair triple =>
    orderedSpacetimeBivectorComponent
        (pointwisePhysicalBivectorCovariantDerivative connection jet
          (threeFormFirst triple))
        internalPair (threeFormSecond triple) (threeFormThird triple) +
      orderedSpacetimeBivectorComponent
        (pointwisePhysicalBivectorCovariantDerivative connection jet
          (threeFormSecond triple))
        internalPair (threeFormThird triple) (threeFormFirst triple) +
      orderedSpacetimeBivectorComponent
        (pointwisePhysicalBivectorCovariantDerivative connection jet
          (threeFormThird triple))
        internalPair (threeFormFirst triple) (threeFormSecond triple)

/-- Exterior derivative of `II+(e)` expressed through arbitrary covariant
coframe-derivative coordinates. -/
def physicalIIPlusExteriorDerivativeOfCoframeDerivative
    (coframe : LorentzianCoframe)
    (covariantDerivative : LorentzianIndex → LorentzianCoframe) :
    PhysicalBivectorThreeForm :=
  fun internalPair triple =>
    orderedSpacetimeBivectorComponent
        (physicalIIPlusCoframeTangent coframe
          (covariantDerivative (threeFormFirst triple)))
        internalPair (threeFormSecond triple) (threeFormThird triple) +
      orderedSpacetimeBivectorComponent
        (physicalIIPlusCoframeTangent coframe
          (covariantDerivative (threeFormSecond triple)))
        internalPair (threeFormThird triple) (threeFormFirst triple) +
      orderedSpacetimeBivectorComponent
        (physicalIIPlusCoframeTangent coframe
          (covariantDerivative (threeFormThird triple)))
        internalPair (threeFormFirst triple) (threeFormSecond triple)

/-- Antisymmetrized covariant coframe derivative. -/
def coframeExteriorTorsion
    (covariantDerivative : LorentzianIndex → LorentzianCoframe)
    (first second internal : LorentzianIndex) : ℝ :=
  covariantDerivative first internal second -
    covariantDerivative second internal first

/-- The undualized three-form `T^I wedge e^J - T^J wedge e^I`. -/
def torsionCoframeWedgeThreeForm
    (coframe : LorentzianCoframe)
    (torsion : LorentzianIndex → LorentzianIndex → LorentzianIndex → ℝ) :
    PhysicalBivectorThreeForm :=
  fun internalPair triple =>
    let internalFirst := pairFirst internalPair
    let internalSecond := pairSecond internalPair
    let first := threeFormFirst triple
    let second := threeFormSecond triple
    let third := threeFormThird triple
    torsion first second internalFirst * coframe internalSecond third +
      torsion second third internalFirst * coframe internalSecond first +
      torsion third first internalFirst * coframe internalSecond second -
      torsion first second internalSecond * coframe internalFirst third -
      torsion second third internalSecond * coframe internalFirst first -
      torsion third first internalSecond * coframe internalFirst second

/-- Internal Hodge dual of a bivector-valued three-form. -/
def internalBivectorDualThreeForm
    (form : PhysicalBivectorThreeForm) : PhysicalBivectorThreeForm :=
  fun internalPair triple =>
    lorentzianCoframeHodge
      (fun sourceInternalPair => form sourceInternalPair triple)
      internalPair

/-- Pure finite-coordinate Cartan identity.  It uses no action, equation, or
solution: the exterior `II+` derivative of any coframe derivative equals the
internal dual of its torsion--coframe wedge. -/
theorem physicalIIPlusExteriorDerivative_eq_torsionCoframe
    (coframe : LorentzianCoframe)
    (covariantDerivative : LorentzianIndex → LorentzianCoframe) :
    physicalIIPlusExteriorDerivativeOfCoframeDerivative
        coframe covariantDerivative =
      internalBivectorDualThreeForm
        (torsionCoframeWedgeThreeForm coframe
          (coframeExteriorTorsion covariantDerivative)) := by
  funext internalPair triple
  fin_cases internalPair <;> fin_cases triple <;>
    simp [physicalIIPlusExteriorDerivativeOfCoframeDerivative,
      orderedSpacetimeBivectorComponent,
      physicalIIPlusCoframeTangent, internalBivectorDual,
      coframeWedgeTangent, internalBivectorDualThreeForm,
      torsionCoframeWedgeThreeForm, coframeExteriorTorsion,
      orientedLorentzBivectorBasisCoefficient,
      lorentzianCoframeHodge, pairFirst, pairSecond,
      threeFormFirst, threeFormSecond, threeFormThird,
      Fin.sum_univ_six] <;>
    ring

theorem pointwisePhysicalIIPlus_exteriorCovariantDerivative_eq_raw
    (jet : PointwiseLorentzianCoframeJet)
    (connection : PointwiseLorentzSpinConnection)
    (connectionSkew : LorentzSkew connection) :
    pointwisePhysicalBivectorExteriorCovariantDerivative connection
        (pointwisePhysicalIIPlusJet jet) =
      physicalIIPlusExteriorDerivativeOfCoframeDerivative jet.coframe
        (pointwiseCoframeCovariantDerivative jet connection) := by
  funext internalPair triple
  unfold pointwisePhysicalBivectorExteriorCovariantDerivative
  unfold physicalIIPlusExteriorDerivativeOfCoframeDerivative
  rw [pointwisePhysicalIIPlus_covariantDerivative jet connection connectionSkew]
  rw [pointwisePhysicalIIPlus_covariantDerivative jet connection connectionSkew]
  rw [pointwisePhysicalIIPlus_covariantDerivative jet connection connectionSkew]

/-- Final formulation-neutral reduction seam:
`D_omega II+(e) = star_internal (T(omega,e) wedge e)` at an arbitrary
pointwise coframe jet on the explicit Lorentz-skew connection domain. -/
theorem pointwisePhysicalIIPlus_exteriorCovariantDerivative_eq_torsionCoframe
    (jet : PointwiseLorentzianCoframeJet)
    (connection : PointwiseLorentzSpinConnection)
    (connectionSkew : LorentzSkew connection) :
    pointwisePhysicalBivectorExteriorCovariantDerivative connection
        (pointwisePhysicalIIPlusJet jet) =
      internalBivectorDualThreeForm
        (torsionCoframeWedgeThreeForm jet.coframe
          (pointwiseCartanTorsion jet connection)) := by
  rw [pointwisePhysicalIIPlus_exteriorCovariantDerivative_eq_raw
    jet connection connectionSkew]
  rw [physicalIIPlusExteriorDerivative_eq_torsionCoframe]
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineResidualLinearPlebanskiTorsionReduction
