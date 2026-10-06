import H0mework.Versions.AB.Chemistry.LAlanineParametric.IntervalStage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.IntervalParameterMap

open SourceGaussianModel ContinuousGradient SourceSignedEvaluator
open LAlanineContinuousPatch.Parametric

def intervalStage2 (fields : Fin 4 → FieldBox) (state : JetBox) (h : Pair) (dh : VectorPair) : JetBox :=
  stage state h dh (rhs (fields 0) state) (1 / 2)

def intervalStage3 (fields : Fin 4 → FieldBox) (state : JetBox) (h : Pair) (dh : VectorPair) : JetBox :=
  stage state h dh (rhs (fields 1) (intervalStage2 fields state h dh)) (1 / 2)

def intervalStage4 (fields : Fin 4 → FieldBox) (state : JetBox) (h : Pair) (dh : VectorPair) : JetBox :=
  stage state h dh (rhs (fields 2) (intervalStage3 fields state h dh)) 1

def intervalRK4Step (fields : Fin 4 → FieldBox) (state : JetBox) (h : Pair) (dh : VectorPair) : JetBox :=
  stage state h dh (combine (rhs (fields 0) state)
    (rhs (fields 1) (intervalStage2 fields state h dh))
    (rhs (fields 2) (intervalStage3 fields state h dh))
    (rhs (fields 3) (intervalStage4 fields state h dh))) (1 / 6)

def FourSourceFields (fields : Fin 4 → FieldBox) (state : JetBox) (h : Pair) (dh : VectorPair) : Prop :=
  (∀ x, VectorHolds state.position x → FieldHolds (fields 0) x) ∧
  (∀ x, VectorHolds (intervalStage2 fields state h dh).position x → FieldHolds (fields 1) x) ∧
  (∀ x, VectorHolds (intervalStage3 fields state h dh).position x → FieldHolds (fields 2) x) ∧
  (∀ x, VectorHolds (intervalStage4 fields state h dh).position x → FieldHolds (fields 3) x)

set_option maxRecDepth 2048 in
theorem intervalRK4Step_contains (fields : Fin 4 → FieldBox) (state : JetBox) (h : Pair) (dh : VectorPair)
    (certified : FourSourceFields fields state h dh)
    (x : Point) (J : Point →L[ℝ] Point) (scalar : ℝ) (scalarDerivative : Point →L[ℝ] ℝ)
    (input : JetHolds state x J) (stepBound : Holds h scalar)
    (parameterBound : ∀ j, Holds (dh j) (scalarDerivative (Pi.single j 1))) :
    JetHolds (intervalRK4Step fields state h dh) (rk4Step sourceGradient scalar x)
      (rk4Derivative sourceGradient sourceHessianLinear scalar scalarDerivative x J) := by
  have first := rhs_contains (fields 0) state x J input (certified.1 x input.1)
  have secondInput := stage_contains state _ h dh (1 / 2) x _ J _ scalar scalarDerivative
    input first stepBound parameterBound
  have second := rhs_contains (fields 1) _ _ _ secondInput (certified.2.1 _ secondInput.1)
  have thirdInput := stage_contains state _ h dh (1 / 2) x _ J _ scalar scalarDerivative
    input second stepBound parameterBound
  have third := rhs_contains (fields 2) _ _ _ thirdInput (certified.2.2.1 _ thirdInput.1)
  have fourthInput := stage_contains state _ h dh 1 x _ J _ scalar scalarDerivative
    input third stepBound parameterBound
  have fourth := rhs_contains (fields 3) _ _ _ fourthInput (certified.2.2.2 _ fourthInput.1)
  have total := combine_contains _ _ _ _ _ _ _ _ _ _ _ _ first second third fourth
  have output := stage_contains state _ h dh (1 / 6) x _ J _ scalar scalarDerivative
    input total stepBound parameterBound
  simpa only [intervalRK4Step, intervalStage2, intervalStage3, intervalStage4,
    rk4Step, rk4Derivative, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, one_mul, one_div_mul_eq_div] using output

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.IntervalParameterMap
