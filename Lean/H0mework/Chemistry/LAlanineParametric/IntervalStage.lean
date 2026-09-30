import H0mework.Chemistry.LAlanineParametric.IntervalLinear

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.IntervalParameterMap

open SourceGaussianModel ContinuousGradient SourceSignedEvaluator
open LAlanineContinuousPatch.Parametric

structure JetBox where
  position : VectorPair
  derivative : MatrixPair

structure FieldBox where
  gradient : VectorPair
  hessian : MatrixPair

def JetHolds (box : JetBox) (x : Point) (J : Point →L[ℝ] Point) : Prop :=
  VectorHolds box.position x ∧ MatrixHolds box.derivative J

def FieldHolds (box : FieldBox) (x : Point) : Prop :=
  VectorHolds box.gradient (sourceGradient x) ∧ ∀ i j, Holds (box.hessian i j) (sourceHessian x i j)

def rhs (field : FieldBox) (state : JetBox) : JetBox :=
  ⟨field.gradient, matrixMultiply field.hessian state.derivative⟩

def stage (state : JetBox) (h : Pair) (dh : VectorPair) (k : JetBox) (factor : ℚ) : JetBox :=
  ⟨vectorAdd state.position (vectorScale (mul (point factor) h) k.position),
    matrixAdd state.derivative (matrixScale (point factor)
      (matrixAdd (matrixScale h k.derivative) (outer k.position dh)))⟩

theorem rhs_contains (field : FieldBox) (state : JetBox) (x : Point) (J : Point →L[ℝ] Point)
    (input : JetHolds state x J) (fieldBound : FieldHolds field x) :
    JetHolds (rhs field state) (sourceGradient x) ((sourceHessianLinear x).comp J) :=
  ⟨fieldBound.1, hessianMultiply_contains _ _ x J fieldBound.2 input.2⟩

theorem stage_contains (state k : JetBox) (h : Pair) (dh : VectorPair) (factor : ℚ)
    (x value : Point) (J derivative : Point →L[ℝ] Point) (scalar : ℝ) (scalarDerivative : Point →L[ℝ] ℝ)
    (input : JetHolds state x J) (fieldBound : JetHolds k value derivative)
    (stepBound : Holds h scalar) (parameterBound : ∀ j, Holds (dh j) (scalarDerivative (Pi.single j 1))) :
    JetHolds (stage state h dh k factor) (x + ((factor : ℝ) * scalar) • value)
      (stageDerivative scalar scalarDerivative J value derivative (factor : ℝ)) := by
  constructor
  · exact vectorAdd_contains _ _ _ _ input.1
      (vectorScale_contains _ _ _ _ (mul_holds _ _ _ _ (point_holds factor) stepBound) fieldBound.1)
  · exact matrixAdd_contains _ _ _ _ input.2
      (matrixScale_contains _ _ _ _ (point_holds factor)
        (matrixAdd_contains _ _ _ _ (matrixScale_contains _ _ _ _ stepBound fieldBound.2)
          (outer_contains _ _ value scalarDerivative fieldBound.1 parameterBound)))

def vectorCombine (a b c d : VectorPair) : VectorPair :=
  vectorAdd (vectorAdd (vectorAdd a (vectorScale (point 2) b)) (vectorScale (point 2) c)) d

def matrixCombine (a b c d : MatrixPair) : MatrixPair :=
  matrixAdd (matrixAdd (matrixAdd a (matrixScale (point 2) b)) (matrixScale (point 2) c)) d

def combine (a b c d : JetBox) : JetBox :=
  ⟨vectorCombine a.position b.position c.position d.position,
    matrixCombine a.derivative b.derivative c.derivative d.derivative⟩

theorem combine_contains (a b c d : JetBox) (xa xb xc xd : Point)
    (ja jb jc jd : Point →L[ℝ] Point)
    (ha : JetHolds a xa ja) (hb : JetHolds b xb jb) (hc : JetHolds c xc jc) (hd : JetHolds d xd jd) :
    JetHolds (combine a b c d) (xa + 2 • xb + 2 • xc + xd) (ja + 2 • jb + 2 • jc + jd) := by
  constructor
  · simpa only [combine, vectorCombine, Rat.cast_ofNat, two_smul] using
      vectorAdd_contains _ _ _ _ (vectorAdd_contains _ _ _ _ (vectorAdd_contains _ _ _ _ ha.1
        (vectorScale_contains _ _ _ _ (point_holds 2) hb.1))
          (vectorScale_contains _ _ _ _ (point_holds 2) hc.1)) hd.1
  · simpa only [combine, matrixCombine, Rat.cast_ofNat, two_smul] using
      matrixAdd_contains _ _ _ _ (matrixAdd_contains _ _ _ _ (matrixAdd_contains _ _ _ _ ha.2
        (matrixScale_contains _ _ _ _ (point_holds 2) hb.2))
          (matrixScale_contains _ _ _ _ (point_holds 2) hc.2)) hd.2

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.IntervalParameterMap
