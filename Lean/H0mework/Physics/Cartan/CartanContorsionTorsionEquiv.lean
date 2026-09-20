import H0mework.Physics.Coframe.CoframeTwoFormPairing
import H0mework.Physics.Cartan.ResidualLinearPlebanskiTorsionReduction

/-!
# Nondegenerate-coframe Cartan contorsion--torsion equivalence

This module constructs the 24-dimensional antisymmetric torsion carrier and
the explicit, coframe-dependent equivalence

`lowered Lorentz contorsion q <-> vector-valued Cartan torsion increment T`.

The construction first transports both sides into the internal coframe,
applies the fixed Cartan identity

`t_(I,A,B) = K_(A,I,B) - K_(B,I,A)`,

and transports back.  Its inverse is the unique three-cycle formula

`K_(A,I,J) = (t_(I,A,J) - t_(A,J,I) + t_(J,I,A)) / 2`.

Only `det e != 0` is required.  No orientation branch, action, spin current,
source, residual, stationarity receipt, solution, or response witness enters
the constructor.  This is the linear increment map relative to a future
torsion-free baseline; the full connection-to-torsion relation remains
affine and is not conflated with this equivalence.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCartanContorsionTorsionEquiv

open ProofFreeRicherAnholonomicSource
open StageNineCoframeTwoFormPairing
open StageNineGlobalIntegratedAction
open StageNineLorentzConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open scoped Matrix

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

/-- The 24 independent coordinates of a vector-valued spacetime two-form.
The spacetime two-form index is stored only in the six canonical oriented
pairs, so antisymmetry is part of the carrier rather than a supplied law. -/
@[ext]
structure PointwiseCartanTorsionTwoForm where
  component : Fin 6 → LorentzianIndex → ℝ

def pointwiseCartanTorsionTwoFormCoordinateEquiv :
    PointwiseCartanTorsionTwoForm ≃
      (Fin 6 → LorentzianIndex → ℝ) where
  toFun := PointwiseCartanTorsionTwoForm.component
  invFun := PointwiseCartanTorsionTwoForm.mk
  left_inv torsion := by cases torsion; rfl
  right_inv _ := rfl

instance : AddCommGroup PointwiseCartanTorsionTwoForm :=
  pointwiseCartanTorsionTwoFormCoordinateEquiv.addCommGroup

instance : Module ℝ PointwiseCartanTorsionTwoForm :=
  pointwiseCartanTorsionTwoFormCoordinateEquiv.module ℝ

instance : CoeFun PointwiseCartanTorsionTwoForm
    (fun _ => Fin 6 → LorentzianIndex → ℝ) :=
  ⟨PointwiseCartanTorsionTwoForm.component⟩

@[simp] theorem pointwiseCartanTorsionTwoForm_zero_apply
    (spacetimePair : Fin 6) (internal : LorentzianIndex) :
    (0 : PointwiseCartanTorsionTwoForm) spacetimePair internal = 0 :=
  rfl

@[simp] theorem pointwiseCartanTorsionTwoForm_add_apply
    (first second : PointwiseCartanTorsionTwoForm)
    (spacetimePair : Fin 6) (internal : LorentzianIndex) :
    (first + second) spacetimePair internal =
      first spacetimePair internal + second spacetimePair internal :=
  rfl

@[simp] theorem pointwiseCartanTorsionTwoForm_smul_apply
    (scalar : ℝ) (torsion : PointwiseCartanTorsionTwoForm)
    (spacetimePair : Fin 6) (internal : LorentzianIndex) :
    (scalar • torsion) spacetimePair internal =
      scalar * torsion spacetimePair internal :=
  rfl

/-- Recover an ordered antisymmetric spacetime component from the six typed
two-form coordinates. -/
def orderedCartanTorsionComponent
    (torsion : PointwiseCartanTorsionTwoForm)
    (internal first second : LorentzianIndex) : ℝ :=
  ∑ spacetimePair : Fin 6,
    torsion spacetimePair internal *
      orientedLorentzBivectorBasisCoefficient spacetimePair first second

@[simp] theorem orderedCartanTorsionComponent_canonical
    (torsion : PointwiseCartanTorsionTwoForm)
    (internal : LorentzianIndex) (spacetimePair : Fin 6) :
    orderedCartanTorsionComponent torsion internal
        (pairFirst spacetimePair) (pairSecond spacetimePair) =
      torsion spacetimePair internal := by
  fin_cases spacetimePair <;>
    simp [orderedCartanTorsionComponent,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, Fin.sum_univ_six]

theorem orderedCartanTorsionComponent_antisymm
    (torsion : PointwiseCartanTorsionTwoForm)
    (internal first second : LorentzianIndex) :
    orderedCartanTorsionComponent torsion internal first second =
      -orderedCartanTorsionComponent torsion internal second first := by
  fin_cases first <;> fin_cases second <;>
    simp [orderedCartanTorsionComponent,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, Fin.sum_univ_six]

@[simp] theorem orderedCartanTorsionComponent_diagonal
    (torsion : PointwiseCartanTorsionTwoForm)
    (internal direction : LorentzianIndex) :
    orderedCartanTorsionComponent torsion internal direction direction = 0 := by
  have antisymm :=
    orderedCartanTorsionComponent_antisymm torsion internal direction direction
  linarith

/-- Pull a lowered Lorentz-bivector one-form into internal-frame one-form
coordinates. -/
def pullbackLorentzBivectorOneForm
    (coframe : LorentzianCoframe)
    (oneForm : LorentzBivectorOneForm) : LorentzBivectorOneForm :=
  fun internalDirection internalPair =>
    ((coframe⁻¹).transpose *ᵥ
      (fun spacetimeDirection => oneForm spacetimeDirection internalPair))
      internalDirection

/-- Push internal-frame one-form coordinates back to spacetime one-form
coordinates. -/
def pushforwardLorentzBivectorOneForm
    (coframe : LorentzianCoframe)
    (oneForm : LorentzBivectorOneForm) : LorentzBivectorOneForm :=
  fun spacetimeDirection internalPair =>
    (coframe.transpose *ᵥ
      (fun internalDirection => oneForm internalDirection internalPair))
      spacetimeDirection

theorem pushforward_pullbackLorentzBivectorOneForm
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (oneForm : LorentzBivectorOneForm) :
    pushforwardLorentzBivectorOneForm coframe
        (pullbackLorentzBivectorOneForm coframe oneForm) = oneForm := by
  funext spacetimeDirection internalPair
  unfold pushforwardLorentzBivectorOneForm
    pullbackLorentzBivectorOneForm
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul coframe (isUnit_iff_ne_zero.mpr nondegenerate)]
  simp

theorem pullback_pushforwardLorentzBivectorOneForm
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (oneForm : LorentzBivectorOneForm) :
    pullbackLorentzBivectorOneForm coframe
        (pushforwardLorentzBivectorOneForm coframe oneForm) = oneForm := by
  funext internalDirection internalPair
  unfold pullbackLorentzBivectorOneForm
    pushforwardLorentzBivectorOneForm
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv coframe (isUnit_iff_ne_zero.mpr nondegenerate)]
  simp

@[simp] theorem pullbackLorentzBivectorOneForm_one
    (oneForm : LorentzBivectorOneForm) :
    pullbackLorentzBivectorOneForm (1 : LorentzianCoframe) oneForm =
      oneForm := by
  funext direction internalPair
  simp [pullbackLorentzBivectorOneForm]

@[simp] theorem pushforwardLorentzBivectorOneForm_one
    (oneForm : LorentzBivectorOneForm) :
    pushforwardLorentzBivectorOneForm (1 : LorentzianCoframe) oneForm =
      oneForm := by
  funext direction internalPair
  simp [pushforwardLorentzBivectorOneForm]

/-- Pull a vector-valued spacetime two-form into internal-frame two-form
coordinates. -/
def pullbackCartanTorsionTwoForm
    (coframe : LorentzianCoframe)
    (torsion : PointwiseCartanTorsionTwoForm) :
    PointwiseCartanTorsionTwoForm :=
  ⟨fun framePair internal =>
    coframeTwoFormLinear (coframe⁻¹).transpose
      (fun spacetimePair => torsion spacetimePair internal) framePair⟩

/-- Push an internal-frame vector-valued two-form back to spacetime
two-form coordinates. -/
def pushforwardCartanTorsionTwoForm
    (coframe : LorentzianCoframe)
    (torsion : PointwiseCartanTorsionTwoForm) :
    PointwiseCartanTorsionTwoForm :=
  ⟨fun spacetimePair internal =>
    coframeTwoFormLinear coframe.transpose
      (fun framePair => torsion framePair internal) spacetimePair⟩

theorem pushforward_pullbackCartanTorsionTwoForm
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (torsion : PointwiseCartanTorsionTwoForm) :
    pushforwardCartanTorsionTwoForm coframe
        (pullbackCartanTorsionTwoForm coframe torsion) = torsion := by
  ext spacetimePair internal
  change
    ((coframeTwoFormLinear coframe.transpose).comp
      (coframeTwoFormLinear (coframe⁻¹).transpose))
        (fun pair => torsion pair internal) spacetimePair =
      torsion spacetimePair internal
  rw [← coframeTwoFormLinear_mul, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul coframe (isUnit_iff_ne_zero.mpr nondegenerate)]
  simp [coframeTwoFormLinear_one]

theorem pullback_pushforwardCartanTorsionTwoForm
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (torsion : PointwiseCartanTorsionTwoForm) :
    pullbackCartanTorsionTwoForm coframe
        (pushforwardCartanTorsionTwoForm coframe torsion) = torsion := by
  ext internalPair internal
  change
    ((coframeTwoFormLinear (coframe⁻¹).transpose).comp
      (coframeTwoFormLinear coframe.transpose))
        (fun pair => torsion pair internal) internalPair =
      torsion internalPair internal
  rw [← coframeTwoFormLinear_mul, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv coframe (isUnit_iff_ne_zero.mpr nondegenerate)]
  simp [coframeTwoFormLinear_one]

@[simp] theorem pullbackCartanTorsionTwoForm_one
    (torsion : PointwiseCartanTorsionTwoForm) :
    pullbackCartanTorsionTwoForm (1 : LorentzianCoframe) torsion =
      torsion := by
  ext pair internal
  simp [pullbackCartanTorsionTwoForm, coframeTwoFormLinear_one]

@[simp] theorem pushforwardCartanTorsionTwoForm_one
    (torsion : PointwiseCartanTorsionTwoForm) :
    pushforwardCartanTorsionTwoForm (1 : LorentzianCoframe) torsion =
      torsion := by
  ext pair internal
  simp [pushforwardCartanTorsionTwoForm, coframeTwoFormLinear_one]

/-- The fixed internal-frame Cartan map
`K_(A,I,B) - K_(B,I,A)`. -/
def internalFrameCartanTorsion
    (contorsion : LorentzBivectorOneForm) :
    PointwiseCartanTorsionTwoForm :=
  ⟨fun pair internal =>
    loweredLorentzBivectorMatrix (contorsion (pairFirst pair))
        internal (pairSecond pair) -
      loweredLorentzBivectorMatrix (contorsion (pairSecond pair))
        internal (pairFirst pair)⟩

/-- Explicit inverse of the fixed internal-frame Cartan map. -/
def internalFrameContorsionOfTorsion
    (torsion : PointwiseCartanTorsionTwoForm) :
    LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    (1 / 2 : ℝ) *
      (orderedCartanTorsionComponent torsion
          (pairFirst internalPair) formDirection (pairSecond internalPair) -
        orderedCartanTorsionComponent torsion formDirection
          (pairSecond internalPair) (pairFirst internalPair) +
        orderedCartanTorsionComponent torsion
          (pairSecond internalPair) (pairFirst internalPair) formDirection)

theorem internalFrameContorsionOfTorsion_leftInverse
    (contorsion : LorentzBivectorOneForm) :
    internalFrameContorsionOfTorsion
        (internalFrameCartanTorsion contorsion) = contorsion := by
  funext formDirection internalPair
  fin_cases formDirection <;> fin_cases internalPair <;>
    simp [internalFrameContorsionOfTorsion,
      internalFrameCartanTorsion, orderedCartanTorsionComponent,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, Fin.sum_univ_six] <;>
    ring

theorem internalFrameContorsionOfTorsion_rightInverse
    (torsion : PointwiseCartanTorsionTwoForm) :
    internalFrameCartanTorsion
        (internalFrameContorsionOfTorsion torsion) = torsion := by
  ext pair internal
  fin_cases internal <;> fin_cases pair <;>
    simp [internalFrameContorsionOfTorsion,
      internalFrameCartanTorsion, orderedCartanTorsionComponent,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, Fin.sum_univ_six] <;>
    ring

/-- Raise/lower the torsion's single internal vector index with the fixed
diagonal Minkowski metric. -/
def minkowskiRaiseCartanTorsion
    (torsion : PointwiseCartanTorsionTwoForm) :
    PointwiseCartanTorsionTwoForm :=
  ⟨fun pair internal => minkowskiInternalSign internal * torsion pair internal⟩

@[simp] theorem minkowskiRaiseCartanTorsion_involutive
    (torsion : PointwiseCartanTorsionTwoForm) :
    minkowskiRaiseCartanTorsion (minkowskiRaiseCartanTorsion torsion) =
      torsion := by
  ext pair internal
  fin_cases internal <;>
    simp [minkowskiRaiseCartanTorsion, minkowskiInternalSign]

/-- The coframe-dependent algebraic Cartan coordinate map, factored through
internal-frame coordinates.  Its equality with the existing actual
`pointwiseCartanTorsion` readout is a separate downstream seam. -/
def cartanTorsionOfContorsion
    (coframe : LorentzianCoframe)
    (contorsion : LorentzBivectorOneForm) :
    PointwiseCartanTorsionTwoForm :=
  pushforwardCartanTorsionTwoForm coframe
    (minkowskiRaiseCartanTorsion
      (internalFrameCartanTorsion
        (pullbackLorentzBivectorOneForm coframe contorsion)))

/-- Explicit coframe-dependent inverse from typed torsion coordinates to
lowered Lorentz-bivector contorsion coordinates. -/
def contorsionOfCartanTorsion
    (coframe : LorentzianCoframe)
    (torsion : PointwiseCartanTorsionTwoForm) :
    LorentzBivectorOneForm :=
  pushforwardLorentzBivectorOneForm coframe
    (internalFrameContorsionOfTorsion
      (minkowskiRaiseCartanTorsion
        (pullbackCartanTorsionTwoForm coframe torsion)))

theorem contorsionOfCartanTorsion_leftInverse
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (contorsion : LorentzBivectorOneForm) :
    contorsionOfCartanTorsion coframe
        (cartanTorsionOfContorsion coframe contorsion) = contorsion := by
  unfold contorsionOfCartanTorsion cartanTorsionOfContorsion
  rw [pullback_pushforwardCartanTorsionTwoForm coframe nondegenerate,
    minkowskiRaiseCartanTorsion_involutive,
    internalFrameContorsionOfTorsion_leftInverse,
    pushforward_pullbackLorentzBivectorOneForm coframe nondegenerate]

theorem contorsionOfCartanTorsion_rightInverse
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (torsion : PointwiseCartanTorsionTwoForm) :
    cartanTorsionOfContorsion coframe
        (contorsionOfCartanTorsion coframe torsion) = torsion := by
  unfold contorsionOfCartanTorsion cartanTorsionOfContorsion
  rw [pullback_pushforwardLorentzBivectorOneForm coframe nondegenerate,
    internalFrameContorsionOfTorsion_rightInverse,
    minkowskiRaiseCartanTorsion_involutive,
    pushforward_pullbackCartanTorsionTwoForm coframe nondegenerate]

theorem pullbackLorentzBivectorOneForm_add
    (coframe : LorentzianCoframe)
    (first second : LorentzBivectorOneForm) :
    pullbackLorentzBivectorOneForm coframe (first + second) =
      pullbackLorentzBivectorOneForm coframe first +
        pullbackLorentzBivectorOneForm coframe second := by
  funext direction internalPair
  simp [pullbackLorentzBivectorOneForm, Matrix.mulVec, dotProduct,
    mul_add, Finset.sum_add_distrib]

theorem pullbackLorentzBivectorOneForm_smul
    (coframe : LorentzianCoframe) (scalar : ℝ)
    (oneForm : LorentzBivectorOneForm) :
    pullbackLorentzBivectorOneForm coframe (scalar • oneForm) =
      scalar • pullbackLorentzBivectorOneForm coframe oneForm := by
  funext direction internalPair
  simp [pullbackLorentzBivectorOneForm, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

theorem internalFrameCartanTorsion_add
    (first second : LorentzBivectorOneForm) :
    internalFrameCartanTorsion (first + second) =
      internalFrameCartanTorsion first +
        internalFrameCartanTorsion second := by
  ext pair internal
  simp [internalFrameCartanTorsion, loweredLorentzBivectorMatrix,
    add_mul, Finset.sum_add_distrib]
  ring

theorem internalFrameCartanTorsion_smul
    (scalar : ℝ) (contorsion : LorentzBivectorOneForm) :
    internalFrameCartanTorsion (scalar • contorsion) =
      scalar • internalFrameCartanTorsion contorsion := by
  ext pair internal
  simp only [internalFrameCartanTorsion,
    loweredLorentzBivectorMatrix,
    pointwiseCartanTorsionTwoForm_smul_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro index _
    ring
  · apply Finset.sum_congr rfl
    intro index _
    ring

theorem minkowskiRaiseCartanTorsion_add
    (first second : PointwiseCartanTorsionTwoForm) :
    minkowskiRaiseCartanTorsion (first + second) =
      minkowskiRaiseCartanTorsion first +
        minkowskiRaiseCartanTorsion second := by
  ext pair internal
  simp [minkowskiRaiseCartanTorsion, mul_add]

theorem minkowskiRaiseCartanTorsion_smul
    (scalar : ℝ) (torsion : PointwiseCartanTorsionTwoForm) :
    minkowskiRaiseCartanTorsion (scalar • torsion) =
      scalar • minkowskiRaiseCartanTorsion torsion := by
  ext pair internal
  simp [minkowskiRaiseCartanTorsion]
  ring

theorem pushforwardCartanTorsionTwoForm_add
    (coframe : LorentzianCoframe)
    (first second : PointwiseCartanTorsionTwoForm) :
    pushforwardCartanTorsionTwoForm coframe (first + second) =
      pushforwardCartanTorsionTwoForm coframe first +
        pushforwardCartanTorsionTwoForm coframe second := by
  ext pair internal
  simp [pushforwardCartanTorsionTwoForm, coframeTwoFormLinear,
    mul_add, Finset.sum_add_distrib]

theorem pushforwardCartanTorsionTwoForm_smul
    (coframe : LorentzianCoframe) (scalar : ℝ)
    (torsion : PointwiseCartanTorsionTwoForm) :
    pushforwardCartanTorsionTwoForm coframe (scalar • torsion) =
      scalar • pushforwardCartanTorsionTwoForm coframe torsion := by
  ext pair internal
  simp [pushforwardCartanTorsionTwoForm, coframeTwoFormLinear,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

theorem cartanTorsionOfContorsion_add
    (coframe : LorentzianCoframe)
    (first second : LorentzBivectorOneForm) :
    cartanTorsionOfContorsion coframe (first + second) =
      cartanTorsionOfContorsion coframe first +
        cartanTorsionOfContorsion coframe second := by
  unfold cartanTorsionOfContorsion
  rw [pullbackLorentzBivectorOneForm_add,
    internalFrameCartanTorsion_add,
    minkowskiRaiseCartanTorsion_add,
    pushforwardCartanTorsionTwoForm_add]

theorem cartanTorsionOfContorsion_smul
    (coframe : LorentzianCoframe) (scalar : ℝ)
    (contorsion : LorentzBivectorOneForm) :
    cartanTorsionOfContorsion coframe (scalar • contorsion) =
      scalar • cartanTorsionOfContorsion coframe contorsion := by
  unfold cartanTorsionOfContorsion
  rw [pullbackLorentzBivectorOneForm_smul,
    internalFrameCartanTorsion_smul,
    minkowskiRaiseCartanTorsion_smul,
    pushforwardCartanTorsionTwoForm_smul]

/-- The no-free-parameter coframe-dependent linear equivalence between
lowered Lorentz contorsion coordinates and typed Cartan torsion increments. -/
def cartanContorsionTorsionLinearEquiv
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    LorentzBivectorOneForm ≃ₗ[ℝ] PointwiseCartanTorsionTwoForm where
  toFun := cartanTorsionOfContorsion coframe
  invFun := contorsionOfCartanTorsion coframe
  left_inv := contorsionOfCartanTorsion_leftInverse coframe nondegenerate
  right_inv := contorsionOfCartanTorsion_rightInverse coframe nondegenerate
  map_add' := cartanTorsionOfContorsion_add coframe
  map_smul' := cartanTorsionOfContorsion_smul coframe

@[simp] theorem cartanContorsionTorsionLinearEquiv_apply
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (contorsion : LorentzBivectorOneForm) :
    cartanContorsionTorsionLinearEquiv coframe nondegenerate contorsion =
      cartanTorsionOfContorsion coframe contorsion :=
  rfl

@[simp] theorem cartanContorsionTorsionLinearEquiv_symm_apply
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (torsion : PointwiseCartanTorsionTwoForm) :
    (cartanContorsionTorsionLinearEquiv coframe nondegenerate).symm torsion =
      contorsionOfCartanTorsion coframe torsion :=
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineCartanContorsionTorsionEquiv
