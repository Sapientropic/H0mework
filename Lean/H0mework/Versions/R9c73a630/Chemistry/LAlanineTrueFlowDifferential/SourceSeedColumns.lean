import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceTimeColumn
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceVariational

/-!
Fixed-time parameter slices identify the seed columns of the actual Jacobian with
the derivative of the original initial-value flow. Together with the source time
column this gives the complete parameter derivative.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient ContinuousSeed TrueTubeWholeActual WholeCellPartition
open Set
noncomputable section

def actualParameterTime (p : BandPoint) : Time := ⟨p.val 2, by
  constructor
  · simpa [fullLower, fullLowerQ, halfFlow_exact] using p.property.1 (2 : Fin 3)
  · simpa [fullUpper, fullUpperQ, halfFlow_exact] using p.property.2 (2 : Fin 3)⟩

/-- Each initial-parameter column is the actual fixed-time initial-value response. -/
theorem trueJacobian_seed_column (p : BandPoint) (j : Fin 3) (hj : j ≠ 2) :
    trueJacobian p (Pi.single j 1) =
      initialFlowDerivative p (actualParameterTime p)
        (bandSeedDerivative 4 (Geometry.Source.epsilon 0) p.val (Pi.single j 1)) := by
  have curve_same : trueParameterMap ∘ Function.update p.val j =
      (fun q => rawPath (ContinuousParameterMap.initialMap 0 4 q) (actualParameterTime p)) ∘
        Function.update p.val j := by
    funext r
    change rawFlow (ContinuousParameterMap.initialMap 0 4 (Function.update p.val j r))
      (Function.update p.val j r 2) =
        rawFlow (ContinuousParameterMap.initialMap 0 4 (Function.update p.val j r)) (p.val 2)
    rw [Function.update_of_ne (Ne.symm hj)]
  have line_inside : MapsTo (Function.update p.val j)
      (Icc (fullLower j) (fullUpper j)) fullDomain := by
    intro r hr
    constructor <;> intro i <;> by_cases hi : i = j
    · subst i
      simpa using hr.1
    · simpa only [Function.update_of_ne hi] using p.property.1 i
    · subst i
      simpa using hr.2
    · simpa only [Function.update_of_ne hi] using p.property.2 i
  have parameter_derivative := (actualMap_hasFDerivWithinAt p).comp_hasDerivWithinAt_of_eq
    (p.val j) (hasDerivAt_update p.val j (p.val j)).hasDerivWithinAt line_inside (by simp)
  rw [curve_same] at parameter_derivative
  have initial_derivative := (initialFlow_hasStrictFDerivAt p (actualParameterTime p)).hasFDerivAt.comp
    p.val (bandSeed_hasFDerivAt 4 (Geometry.Source.epsilon 0) p.val)
  have seed_derivative := initial_derivative.comp_hasDerivAt_of_eq
    (p.val j) (hasDerivAt_update p.val j (p.val j)) (by simp)
  have ordered : fullLower j < fullUpper j := Rat.cast_lt.mpr (full_ordered j)
  have unique := uniqueDiffOn_Icc ordered (p.val j) ⟨p.property.1 j, p.property.2 j⟩
  exact (parameter_derivative.derivWithin unique).symm.trans
    (seed_derivative.hasDerivWithinAt.derivWithin unique)

/-- The full actual Jacobian splits into transported seed variation and original time evolution. -/
theorem trueJacobian_decomposition (p : BandPoint) (h : Point) :
    trueJacobian p h = initialFlowDerivative p (actualParameterTime p)
      (bandSeedDerivative 4 (Geometry.Source.epsilon 0) p.val h) +
        h 2 • sourceGradient (trueParameterMap p.val) := by
  let response : Point →L[ℝ] Point :=
    (initialFlowDerivative p (actualParameterTime p)).comp
        (bandSeedDerivative 4 (Geometry.Source.epsilon 0) p.val) +
      (ContinuousLinearMap.proj 2).smulRight (sourceGradient (trueParameterMap p.val))
  have columns (j : Fin 3) : trueJacobian p (Pi.single j 1) = response (Pi.single j 1) := by
    by_cases hj : j = 2
    · subst j
      rw [trueJacobian_time_column]
      simp [response, bandSeedDerivative, bandUDerivative]
    · rw [trueJacobian_seed_column p j hj]
      simp [response, Pi.single_eq_of_ne (Ne.symm hj)]
  have equality : (trueJacobian p).toLinearMap = response.toLinearMap := by
    apply LinearMap.pi_ext
    intro j r
    have basis : Pi.single j r = r • Pi.single j (1 : ℝ) := by
      ext i
      by_cases hi : i = j <;> simp [hi]
    change trueJacobian p (Pi.single j r) = response (Pi.single j r)
    rw [basis, map_smul, map_smul, columns]
  exact LinearMap.congr_fun equality h

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
