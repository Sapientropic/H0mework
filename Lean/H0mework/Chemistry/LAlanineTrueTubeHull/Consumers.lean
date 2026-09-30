import H0mework.Chemistry.LAlanineTrueTubeHull.Amplification
import H0mework.Chemistry.LAlanineTrueTubeWhole.ChecksSupport

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeHull

open SourceGaussianModel SourceSignedEvaluator TrueTubeTrace
noncomputable section

theorem whole_call_gradient_distance (i : WholeCellSource.Field) (c : TrueTubeSource.Call)
    (x y : Point) (wholeInside : InRectangle (WholeCellSource.box i) x)
    (callInside : InRectangle (TrueTubeSource.callBox c) y) :
    dist (ContinuousGradient.sourceGradient x) (ContinuousGradient.sourceGradient y) ≤
      (lipschitzConstant : ℝ) * dist x y :=
  common_lipschitz.dist_le_mul x
    ((inRectangle_iff _ _).mp (TrueTubeHullSource.whole_contains i x wholeInside)) y
    ((inRectangle_iff _ _).mp (TrueTubeHullSource.call_contains c y callInside))

theorem actual_tube_contains (d : TrueTubeSource.Direction) (i : TrueTubeSource.Step)
    (x : Point) (inside : InRectangle (TrueTubeSource.tubeBox d i) x) :
    InRectangle TrueTubeHullSource.box x :=
  TrueTubeHullSource.call_contains (TrueTubeWholeSource.tubeCallAt d i) x
    ((TrueTubeWholeChecks.tube_call_box d i).symm ▸ inside)

theorem actual_initial_contains (d : TrueTubeSource.Direction) (i : TrueTubeSource.Step)
    (x : Point) (inside : InRectangle (TrueTubeSource.initialBox d i) x) :
    InRectangle TrueTubeHullSource.box x :=
  TrueTubeHullSource.call_contains (TrueTubeWholeSource.initialCallAt d i) x
    ((TrueTubeWholeChecks.initial_call_box d i).symm ▸ inside)

end
end LAlanine40K2025.BasinRefinement.TrueTubeHull
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
