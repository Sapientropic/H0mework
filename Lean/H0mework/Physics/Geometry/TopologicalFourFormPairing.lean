import H0mework.Physics.Coframe.CoframeTwoFormPairing

/-!
# Metric-free oriented four-form pairing

This module fixes the finite-coordinate coefficient of the spacetime wedge
product independently of a coframe, metric, Hodge operator, volume density,
source, action, or field equation.  The oriented two-form basis is

`(01, 02, 03, 23, 31, 12)`

and the orientation convention is `epsilon_0123 = +1`.  Consequently every
complementary two-form pair contributes with positive sign.

The gravity pairing contracts two contravariant internal bivectors with the
induced Lorentz signs exactly once.  Historical lowered gravity curvature
must therefore pass through the separate COV-1 variance normalization before
it is used as the second argument; variance is not a caller-selectable sign.

The final identity records the exact convention seam with the historical
dynamical-pairing expression at the identity coframe.  It is a negative seam,
not an authorization to use the historical coframe-dependent expression as a
topological pairing away from the identity slice.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineTopologicalFourFormPairing

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCoframeTwoFormPairing
open StageNineGlobalIntegratedAction

noncomputable section

set_option autoImplicit false

/-- Complementary oriented spacetime two-form coordinate. -/
def twoFormComplement : Fin 6 → Fin 6 := ![3, 4, 5, 0, 1, 2]

@[simp] theorem twoFormComplement_involutive (pair : Fin 6) :
    twoFormComplement (twoFormComplement pair) = pair := by
  fin_cases pair <;> rfl

/-- Generic coefficient of the wedge of two fiber-valued two-forms.  The
fiber pairing supplies only the sector contraction; all spacetime orientation
data are fixed here. -/
def generatedTwoFormWedgeCoefficient
    {V : Type*}
    (fiberPairing : V → V → ℝ)
    (first second : Fin 6 → V) : ℝ :=
  ∑ pair : Fin 6,
    fiberPairing (first pair) (second (twoFormComplement pair))

/-- Metric-free coefficient of `first ∧ second` in the positive oriented
coordinate four-form. -/
def orientedTwoFormWedgeCoefficient
    (first second : GaugeTwoForm) : ℝ :=
  generatedTwoFormWedgeCoefficient (fun x y : ℝ => x * y) first second

theorem orientedTwoFormWedgeCoefficient_explicit
    (first second : GaugeTwoForm) :
    orientedTwoFormWedgeCoefficient first second =
      first 0 * second 3 + first 1 * second 4 +
      first 2 * second 5 + first 3 * second 0 +
      first 4 * second 1 + first 5 * second 2 := by
  simp [orientedTwoFormWedgeCoefficient,
    generatedTwoFormWedgeCoefficient, twoFormComplement, Fin.sum_univ_six]

theorem orientedTwoFormWedgeCoefficient_add_left
    (first second residual : GaugeTwoForm) :
    orientedTwoFormWedgeCoefficient (first + second) residual =
      orientedTwoFormWedgeCoefficient first residual +
        orientedTwoFormWedgeCoefficient second residual := by
  simp only [orientedTwoFormWedgeCoefficient_explicit, Pi.add_apply]
  ring

theorem orientedTwoFormWedgeCoefficient_smul_left
    (parameter : ℝ) (first second : GaugeTwoForm) :
    orientedTwoFormWedgeCoefficient (parameter • first) second =
      parameter * orientedTwoFormWedgeCoefficient first second := by
  simp only [orientedTwoFormWedgeCoefficient_explicit,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem orientedTwoFormWedgeCoefficient_symmetric
    (first second : GaugeTwoForm) :
    orientedTwoFormWedgeCoefficient first second =
      orientedTwoFormWedgeCoefficient second first := by
  simp only [orientedTwoFormWedgeCoefficient_explicit]
  ring

theorem orientedTwoFormWedgeCoefficient_add_right
    (first second residual : GaugeTwoForm) :
    orientedTwoFormWedgeCoefficient residual (first + second) =
      orientedTwoFormWedgeCoefficient residual first +
        orientedTwoFormWedgeCoefficient residual second := by
  rw [orientedTwoFormWedgeCoefficient_symmetric residual,
    orientedTwoFormWedgeCoefficient_add_left,
    orientedTwoFormWedgeCoefficient_symmetric first,
    orientedTwoFormWedgeCoefficient_symmetric second]

theorem orientedTwoFormWedgeCoefficient_smul_right
    (parameter : ℝ) (first second : GaugeTwoForm) :
    orientedTwoFormWedgeCoefficient first (parameter • second) =
      parameter * orientedTwoFormWedgeCoefficient first second := by
  rw [orientedTwoFormWedgeCoefficient_symmetric first,
    orientedTwoFormWedgeCoefficient_smul_left,
    orientedTwoFormWedgeCoefficient_symmetric second]

@[simp] theorem orientedTwoFormWedgeCoefficient_zero_left
    (second : GaugeTwoForm) :
    orientedTwoFormWedgeCoefficient 0 second = 0 := by
  simp [orientedTwoFormWedgeCoefficient_explicit]

@[simp] theorem orientedTwoFormWedgeCoefficient_zero_right
    (first : GaugeTwoForm) :
    orientedTwoFormWedgeCoefficient first 0 = 0 := by
  rw [orientedTwoFormWedgeCoefficient_symmetric]
  exact orientedTwoFormWedgeCoefficient_zero_left first

/-- Coordinate basis two-form used only to prove normalization and
nondegeneracy of the pairing. -/
def twoFormCoordinateBasis (pair : Fin 6) : GaugeTwoForm :=
  Pi.single pair 1

@[simp] theorem orientedTwoFormWedgeCoefficient_basis_zero_three :
    orientedTwoFormWedgeCoefficient
        (twoFormCoordinateBasis 0) (twoFormCoordinateBasis 3) = 1 := by
  simp (disch := decide) [orientedTwoFormWedgeCoefficient_explicit,
    twoFormCoordinateBasis]

theorem orientedTwoFormWedgeCoefficient_separates_left
    (first : GaugeTwoForm)
    (annihilates : ∀ second : GaugeTwoForm,
      orientedTwoFormWedgeCoefficient first second = 0) :
    first = 0 := by
  funext pair
  fin_cases pair
  · simpa (disch := decide) [orientedTwoFormWedgeCoefficient_explicit,
      twoFormCoordinateBasis, Pi.single_apply] using
        annihilates (twoFormCoordinateBasis 3)
  · simpa (disch := decide) [orientedTwoFormWedgeCoefficient_explicit,
      twoFormCoordinateBasis, Pi.single_apply] using
        annihilates (twoFormCoordinateBasis 4)
  · simpa (disch := decide) [orientedTwoFormWedgeCoefficient_explicit,
      twoFormCoordinateBasis, Pi.single_apply] using
        annihilates (twoFormCoordinateBasis 5)
  · simpa (disch := decide) [orientedTwoFormWedgeCoefficient_explicit,
      twoFormCoordinateBasis, Pi.single_apply] using
        annihilates (twoFormCoordinateBasis 0)
  · simpa (disch := decide) [orientedTwoFormWedgeCoefficient_explicit,
      twoFormCoordinateBasis, Pi.single_apply] using
        annihilates (twoFormCoordinateBasis 1)
  · simpa (disch := decide) [orientedTwoFormWedgeCoefficient_explicit,
      twoFormCoordinateBasis, Pi.single_apply] using
        annihilates (twoFormCoordinateBasis 2)

/-- Metric-free gravity wedge coefficient.  The internal Lorentz contraction
appears exactly once; the spacetime wedge carries no metric sign. -/
def gravityTopologicalWedgeCoefficient
    (first second : PhysicalBivector) : ℝ :=
  ∑ internalPair : Fin 6,
    lorentzianTwoFormSign internalPair *
      orientedTwoFormWedgeCoefficient
        (first internalPair) (second internalPair)

theorem gravityTopologicalWedgeCoefficient_add_left
    (first second residual : PhysicalBivector) :
    gravityTopologicalWedgeCoefficient (first + second) residual =
      gravityTopologicalWedgeCoefficient first residual +
        gravityTopologicalWedgeCoefficient second residual := by
  unfold gravityTopologicalWedgeCoefficient
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro internalPair _
  rw [show (first + second) internalPair =
      first internalPair + second internalPair by rfl,
    orientedTwoFormWedgeCoefficient_add_left]
  ring

theorem gravityTopologicalWedgeCoefficient_smul_left
    (parameter : ℝ) (first second : PhysicalBivector) :
    gravityTopologicalWedgeCoefficient (parameter • first) second =
      parameter * gravityTopologicalWedgeCoefficient first second := by
  unfold gravityTopologicalWedgeCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro internalPair _
  rw [show (parameter • first) internalPair =
      parameter • first internalPair by rfl,
    orientedTwoFormWedgeCoefficient_smul_left]
  ring

theorem gravityTopologicalWedgeCoefficient_symmetric
    (first second : PhysicalBivector) :
    gravityTopologicalWedgeCoefficient first second =
      gravityTopologicalWedgeCoefficient second first := by
  unfold gravityTopologicalWedgeCoefficient
  apply Finset.sum_congr rfl
  intro internalPair _
  rw [orientedTwoFormWedgeCoefficient_symmetric]

/-- The internal Lorentz Hodge is self-adjoint for the metric-free gravity
wedge pairing.  This is a finite-coordinate representation identity: it
requires no coframe, nondegeneracy, source, action, or equation premise. -/
theorem gravityTopologicalWedgeCoefficient_internalDual_symmetric
    (first second : PhysicalBivector) :
    gravityTopologicalWedgeCoefficient first
        (gravityInternalDualEquiv second) =
      gravityTopologicalWedgeCoefficient second
        (gravityInternalDualEquiv first) := by
  simp [gravityTopologicalWedgeCoefficient,
    gravityInternalDualEquiv, gravityInternalDualLinear,
    internalBivectorDual, lorentzianCoframeHodge,
    orientedTwoFormWedgeCoefficient_explicit,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, Fin.sum_univ_six]
  ring

theorem gravityTopologicalWedgeCoefficient_add_right
    (first second residual : PhysicalBivector) :
    gravityTopologicalWedgeCoefficient residual (first + second) =
      gravityTopologicalWedgeCoefficient residual first +
        gravityTopologicalWedgeCoefficient residual second := by
  rw [gravityTopologicalWedgeCoefficient_symmetric residual,
    gravityTopologicalWedgeCoefficient_add_left,
    gravityTopologicalWedgeCoefficient_symmetric first,
    gravityTopologicalWedgeCoefficient_symmetric second]

theorem gravityTopologicalWedgeCoefficient_smul_right
    (parameter : ℝ) (first second : PhysicalBivector) :
    gravityTopologicalWedgeCoefficient first (parameter • second) =
      parameter * gravityTopologicalWedgeCoefficient first second := by
  rw [gravityTopologicalWedgeCoefficient_symmetric first,
    gravityTopologicalWedgeCoefficient_smul_left,
    gravityTopologicalWedgeCoefficient_symmetric second]

@[simp] theorem gravityTopologicalWedgeCoefficient_zero_left
    (second : PhysicalBivector) :
    gravityTopologicalWedgeCoefficient 0 second = 0 := by
  unfold gravityTopologicalWedgeCoefficient
  simp

@[simp] theorem gravityTopologicalWedgeCoefficient_zero_right
    (first : PhysicalBivector) :
    gravityTopologicalWedgeCoefficient first 0 = 0 := by
  rw [gravityTopologicalWedgeCoefficient_symmetric]
  exact gravityTopologicalWedgeCoefficient_zero_left first

/-- Install one spacetime two-form in one internal-pair coordinate. -/
def singleInternalPhysicalBivector
    (internalPair : Fin 6) (form : GaugeTwoForm) : PhysicalBivector :=
  fun candidate => if candidate = internalPair then form else 0

/-- Coordinate lookalike regression: the internal dual in the cross pairing
cannot be silently omitted.  The two inputs have disjoint internal support,
so the undualized pairing is zero, while the correctly dualized pairing is
nonzero. -/
theorem gravityTopologicalWedgeCoefficient_internalDual_not_omittable :
    gravityTopologicalWedgeCoefficient
        (singleInternalPhysicalBivector 0 (twoFormCoordinateBasis 0))
        (gravityInternalDualEquiv
          (singleInternalPhysicalBivector 3 (twoFormCoordinateBasis 3))) =
        -1 ∧
      gravityTopologicalWedgeCoefficient
        (singleInternalPhysicalBivector 0 (twoFormCoordinateBasis 0))
        (singleInternalPhysicalBivector 3 (twoFormCoordinateBasis 3)) = 0 := by
  constructor <;>
    simp (disch := decide)
      [gravityTopologicalWedgeCoefficient,
        gravityInternalDualEquiv, gravityInternalDualLinear,
        internalBivectorDual, lorentzianCoframeHodge,
        orientedTwoFormWedgeCoefficient_explicit,
        singleInternalPhysicalBivector, twoFormCoordinateBasis,
        lorentzianTwoFormSign, minkowskiInternalSign,
        pairFirst, pairSecond, Fin.sum_univ_six]

theorem gravityTopologicalWedgeCoefficient_single_right
    (first : PhysicalBivector) (internalPair : Fin 6)
    (form : GaugeTwoForm) :
    gravityTopologicalWedgeCoefficient first
        (singleInternalPhysicalBivector internalPair form) =
      lorentzianTwoFormSign internalPair *
        orientedTwoFormWedgeCoefficient (first internalPair) form := by
  classical
  unfold gravityTopologicalWedgeCoefficient
    singleInternalPhysicalBivector
  rw [Finset.sum_eq_single internalPair]
  · simp
  · intro candidate _ candidate_ne
    simp [candidate_ne]
  · simp

private theorem lorentzianTwoFormSign_ne_zero (pair : Fin 6) :
    lorentzianTwoFormSign pair ≠ 0 := by
  have square : lorentzianTwoFormSign pair ^ 2 = 1 := by
    fin_cases pair <;>
      simp [lorentzianTwoFormSign, minkowskiInternalSign,
        pairFirst, pairSecond]
  intro equality
  rw [equality] at square
  norm_num at square

theorem gravityTopologicalWedgeCoefficient_separates_left
    (first : PhysicalBivector)
    (annihilates : ∀ second : PhysicalBivector,
      gravityTopologicalWedgeCoefficient first second = 0) :
    first = 0 := by
  funext internalPair
  apply orientedTwoFormWedgeCoefficient_separates_left
  intro form
  have equality := annihilates
    (singleInternalPhysicalBivector internalPair form)
  rw [gravityTopologicalWedgeCoefficient_single_right] at equality
  exact (mul_eq_zero.mp equality).resolve_left
    (lorentzianTwoFormSign_ne_zero internalPair)

/-- Faithful algebraic dual induced by the gravity topological pairing. -/
def gravityTopologicalWedgeDual
    (first : PhysicalBivector) : Module.Dual ℝ PhysicalBivector where
  toFun := fun second => gravityTopologicalWedgeCoefficient first second
  map_add' := fun second residual =>
    gravityTopologicalWedgeCoefficient_add_right second residual first
  map_smul' := by
    intro parameter second
    exact gravityTopologicalWedgeCoefficient_smul_right
      parameter first second

theorem gravityTopologicalWedgeDual_eq_zero_iff
    (first : PhysicalBivector) :
    gravityTopologicalWedgeDual first = 0 ↔ first = 0 := by
  constructor
  · intro equality
    apply gravityTopologicalWedgeCoefficient_separates_left first
    intro second
    have applied := LinearMap.congr_fun equality second
    simpa [gravityTopologicalWedgeDual] using applied
  · rintro rfl
    ext second
    simp [gravityTopologicalWedgeDual]

theorem gravityTopologicalWedgeDual_ne_zero_iff
    (first : PhysicalBivector) :
    gravityTopologicalWedgeDual first ≠ 0 ↔ first ≠ 0 := by
  exact not_congr (gravityTopologicalWedgeDual_eq_zero_iff first)

/-- Exact identity-slice convention seam with the historical dynamical
pairing.  The minus sign is forced by the fixed Lorentzian Hodge table and the
positive lower orientation `epsilon_0123 = +1`. -/
theorem gravityCoframePairing_one_spacetimeHodge_eq_neg_topological
    (first second : PhysicalBivector) :
    gravityCoframePairing (1 : LorentzianCoframe) first
        (gravitySpacetimeHodge (1 : LorentzianCoframe) second) =
      -gravityTopologicalWedgeCoefficient first second := by
  rw [gravityCoframePairing_one_eq_coordinate,
    gravitySpacetimeHodge_one_eq_fixed]
  simp [gravityCoordinatePairing,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, lorentzianCoframeHodge,
    Fin.sum_univ_six]
  ring

end

end SaturationMonoid.PhysicsCore.StageNineTopologicalFourFormPairing
