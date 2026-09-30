import H0mework.Chemistry.LAlanineTrueTubeWhole.ActualFullModel
import H0mework.Chemistry.LAlanineTrueTube.ErrorStarts

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeError

open SourceGaussianModel ContinuousGradient ContinuousParameterMap WholeCellPartition
open TrueTubeError TrueTubeWholeActual Set
noncomputable section

attribute [local irreducible] parameterMap parameterJacobian

def wholeDefectBound : ℚ :=
  max (quarterDefectBound 0) (max (quarterDefectBound 1) (max (quarterDefectBound 2) (quarterDefectBound 3)))

theorem quarter_defect_le (q : Quarter) : quarterDefectBound q ≤ wholeDefectBound := by
  fin_cases q
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  · exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

theorem wholeDefectBound_nonnegative : 0 ≤ wholeDefectBound :=
  (quarterDefectBound_nonneg 0).trans (quarter_defect_le 0)

theorem zero_line_mem_full (p : BandPoint) (t : ℝ) (time : t ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    parameterLine (zeroTimeParameters p.val) t ∈ fullDomain := by
  constructor <;> intro i
  · fin_cases i
    · simpa [parameterLine, zeroTimeParameters] using p.property.1 0
    · simpa [parameterLine, zeroTimeParameters] using p.property.1 1
    · simpa [parameterLine, zeroTimeParameters, fullLower, fullLowerQ, halfFlow_exact] using time.1
  · fin_cases i
    · simpa [parameterLine, zeroTimeParameters] using p.property.2 0
    · simpa [parameterLine, zeroTimeParameters] using p.property.2 1
    · simpa [parameterLine, zeroTimeParameters, fullUpper, fullUpperQ, halfFlow_exact] using time.2

theorem full_defect_norm_le (p : Point) (inside : p ∈ fullDomain) :
    ‖parameterJacobian 0 4 p (Pi.single 2 1) - sourceGradient (parameterMap 0 4 p)‖ ≤
      (wholeDefectBound : ℝ) := by
  rw [fullDomain_eq_iUnion_quarters] at inside
  obtain ⟨q, hq⟩ := mem_iUnion.mp inside
  exact (actual_defect_norm_le q p hq).trans (Rat.cast_le.mpr (quarter_defect_le q))

theorem finite_defect_norm_le (p : BandPoint) (t : ℝ) (time : t ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    ‖finiteVelocity (zeroTimeParameters p.val) t -
      sourceGradient (finiteTrajectory (zeroTimeParameters p.val) t)‖ ≤ (wholeDefectBound : ℝ) :=
  full_defect_norm_le _ (zero_line_mem_full p t time)

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeError
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
