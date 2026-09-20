import H0mework.Physics.Geometry.CanonicalTimePrimitiveSegmentRegularity
import H0mework.Physics.Jets.RadialCurveIntegralFirstJet

/-!
# Smooth regularity of action-owned radial compilers

The finite-order fixed-interval calculus already generates every derivative
of a jointly smooth integrand.  This module packages that mechanism for the
source-anchored radial curve integral.  No closedness, target jet, derivative,
or domination bound is supplied at the public mouth.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineRadialCurveIntegralSmoothRegularity

open MeasureTheory Set
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalTimePrimitiveSegmentRegularity

open scoped ContDiff

noncomputable section

set_option autoImplicit false

/-- A smooth emitted one-form generates a smooth radial primitive.  The
finite-order parameter-integral theorem internally generates every required
derivative and compact domination bound. -/
theorem radialCurveIntegral_contDiff_infty_of_contDiff
    {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (oneForm : BasePoint → BasePoint →L[ℝ] F)
    (regular : ContDiff ℝ ∞ oneForm) :
    ContDiff ℝ ∞
      (fun endpoint ↦ ∫ᶜ x in Path.segment (0 : BasePoint) endpoint, oneForm x) := by
  rw [contDiff_iff_contDiffAt]
  intro contact
  rw [contDiffAt_infty]
  intro order
  let family : BasePoint × ℝ → F :=
    fun pair ↦ oneForm (pair.2 • pair.1) pair.1
  have familySmooth : ContDiff ℝ ∞ family := by
    dsimp [family]
    fun_prop
  have finiteOrder : ((order : ℕ∞ω) + 1) ≤ ∞ := by
    change (((order : ℕ∞) + 1 : ℕ∞) : ℕ∞ω) ≤
      (((⊤ : ℕ∞) : ℕ∞ω))
    exact WithTop.coe_le_coe.mpr le_top
  have generated :=
    fixedIntervalParameterIntegral_contDiffAt_of_contDiffOn_graph
      order family Set.univ isOpen_univ
        (familySmooth.contDiffOn.of_le finiteOrder) contact
        (by intro pair _; exact Set.mem_univ pair)
  have primitive_eq :
      (fun endpoint ↦
        ∫ᶜ x in Path.segment (0 : BasePoint) endpoint, oneForm x) =
        fixedIntervalParameterIntegral family := by
    funext endpoint
    simp [fixedIntervalParameterIntegral, family, curveIntegral_segment,
      AffineMap.lineMap_apply]
  rw [primitive_eq]
  exact generated

end
end
  SaturationMonoid.PhysicsCore.StageNineRadialCurveIntegralSmoothRegularity
