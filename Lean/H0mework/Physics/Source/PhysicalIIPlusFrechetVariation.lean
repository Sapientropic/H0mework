import H0mework.Physics.Holonomic.AnholonomicSource

/-!
# Genuine Fréchet variation of the physical II+ substitution

This module identifies a coframe with its 16-dimensional Euclidean coordinate
vector and the physical bivector `*internal(e ∧ e)` with its 36-dimensional
coordinate vector.  The resulting polynomial map is proved `C∞`; its stored
variation is definitionally Mathlib's Fréchet derivative and is proved by
`HasFDerivAt` at every tetrad.

This is the required derivative foundation for a later common Plebanski
action.  It is not yet that action or a stationary-family theorem.
-/

namespace SaturationMonoid.PhysicsCore.PhysicalIIPlusFrechetVariation

open ProofFreeRicherAnholonomicSource

noncomputable section

abbrev TetradVector :=
  EuclideanSpace ℝ (LorentzianIndex × LorentzianIndex)

abbrev BivectorVector := EuclideanSpace ℝ (Fin 6 × Fin 6)

def coframeOfTetradVector (tetrad : TetradVector) : LorentzianCoframe :=
  fun internal coordinate => tetrad (internal, coordinate)

def vectorOfPhysicalBivector
    (bivector : PhysicalBivector) : BivectorVector :=
  WithLp.toLp 2 (fun pair => bivector pair.1 pair.2)

def physicalIIPlusMap (tetrad : TetradVector) : BivectorVector :=
  vectorOfPhysicalBivector
    (physicalIIPlusBivector (coframeOfTetradVector tetrad))

theorem physicalIIPlusMap_contDiff :
    ContDiff ℝ ⊤ physicalIIPlusMap := by
  apply contDiff_piLp'
  rintro ⟨internalPair, spacetimePair⟩
  fin_cases internalPair <;>
    simp [physicalIIPlusMap, vectorOfPhysicalBivector,
      physicalIIPlusBivector, internalBivectorDual, coframeWedge,
      coframeOfTetradVector, lorentzianCoframeHodge]
  all_goals fun_prop

def physicalIIPlusDerivative
    (tetrad : TetradVector) : TetradVector →L[ℝ] BivectorVector :=
  fderiv ℝ physicalIIPlusMap tetrad

theorem actual_physicalIIPlus_derivative (tetrad : TetradVector) :
    HasFDerivAt physicalIIPlusMap
      (physicalIIPlusDerivative tetrad) tetrad :=
  (physicalIIPlusMap_contDiff.differentiable (by simp))
    |>.differentiableAt.hasFDerivAt

def identityTetradVector : TetradVector :=
  WithLp.toLp 2 (fun pair => (1 : LorentzianCoframe) pair.1 pair.2)

theorem identityTetradVector_physical_component :
    physicalIIPlusMap identityTetradVector (3, 0) = -1 := by
  change physicalIIPlusBivector (1 : LorentzianCoframe) 3 0 = -1
  exact physicalIIPlusBivector_identity_component

theorem zeroTetradVector_physical_component :
    physicalIIPlusMap 0 (3, 0) = 0 := by
  change physicalIIPlusBivector (0 : LorentzianCoframe) 3 0 = 0
  simp [physicalIIPlusBivector, internalBivectorDual, coframeWedge,
    lorentzianCoframeHodge]

theorem physicalIIPlusMap_not_constant :
    ¬ ∀ first second, physicalIIPlusMap first = physicalIIPlusMap second := by
  intro hconstant
  have heq := congrArg (fun value : BivectorVector => value (3, 0))
    (hconstant identityTetradVector 0)
  rw [identityTetradVector_physical_component,
    zeroTetradVector_physical_component] at heq
  norm_num at heq

end
end SaturationMonoid.PhysicsCore.PhysicalIIPlusFrechetVariation
