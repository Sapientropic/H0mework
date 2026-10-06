import H0mework.Versions.AB.Chemistry.LAlanineParametric.IntervalRK4

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.IntervalParameterMap

open SourceGaussianModel ContinuousGradient SourceSignedEvaluator
open LAlanineContinuousPatch.Parametric

def fourStepState (fields : Fin 4 → Fin 4 → FieldBox) (initial : JetBox) (h : Pair) (dh : VectorPair) : Fin 5 → JetBox :=
  let first := intervalRK4Step (fields 0) initial h dh
  let second := intervalRK4Step (fields 1) first h dh
  let third := intervalRK4Step (fields 2) second h dh
  let fourth := intervalRK4Step (fields 3) third h dh
  ![initial, first, second, third, fourth]

def fourStepFieldsCertified (fields : Fin 4 → Fin 4 → FieldBox) (initial : JetBox) (h : Pair) (dh : VectorPair) : Prop :=
  ∀ step : Fin 4, FourSourceFields (fields step) (fourStepState fields initial h dh step.castSucc) h dh

set_option maxRecDepth 2048 in
theorem fourStep_contains (fields : Fin 4 → Fin 4 → FieldBox) (initial : JetBox) (h : Pair) (dh : VectorPair)
    (certified : fourStepFieldsCertified fields initial h dh)
    (x : Point) (J : Point →L[ℝ] Point) (scalar : ℝ) (scalarDerivative : Point →L[ℝ] ℝ)
    (input : JetHolds initial x J) (stepBound : Holds h scalar)
    (parameterBound : ∀ j, Holds (dh j) (scalarDerivative (Pi.single j 1))) :
    ∀ step : Fin 5,
      JetHolds (fourStepState fields initial h dh step) (((rk4Step sourceGradient scalar)^[step.val]) x)
        (rk4JetIterate sourceGradient sourceHessianLinear step.val scalar scalarDerivative x J).2 := by
  intro step
  induction step using Fin.induction with
  | zero => exact input
  | succ previous ih =>
    have next := intervalRK4Step_contains (fields previous) _ h dh (certified previous)
      _ _ scalar scalarDerivative ih stepBound parameterBound
    have advance : fourStepState fields initial h dh previous.succ =
        intervalRK4Step (fields previous) (fourStepState fields initial h dh previous.castSucc) h dh := by
      fin_cases previous <;> rfl
    rw [advance]
    simp only [Fin.val_succ, rk4JetIterate, Function.iterate_succ_apply', rk4JetStep]
    rw [← rk4JetIterate, rk4JetIterate_value]
    exact next

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.IntervalParameterMap
