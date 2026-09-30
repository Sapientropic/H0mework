import H0mework.Chemistry.LAlanineTrueTube.ActualProducer
import H0mework.Chemistry.LAlanineTrueTube.ErrorStarts

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeActual

open SourceGaussianModel SourceSignedEvaluator TrueTubeSource TrueTubeTrace TrueTubeChecks
open WholeCellPartition ContinuousParameterMap Set
noncomputable section

def InitialAt (d : Direction) := {x : Point // InRectangle (initialBox d 0) x}
def TargetAt (d : Direction) := {x : Point // InRectangle (initialBox d 1) x}

def firstCurve (d : Direction) (initial : InitialAt d) : ℝ → Point :=
  Classical.choose (actual_first_step d initial.val initial.property)

theorem firstCurve_spec (d : Direction) (initial : InitialAt d) :
    firstCurve d initial 0 = initial.val ∧
      (∀ t ∈ Icc 0 (stepSize : ℝ),
        HasDerivWithinAt (firstCurve d initial) (signedGradient (sign d) (firstCurve d initial t))
          (Icc 0 (stepSize : ℝ)) t ∧ InRectangle (tubeBox d 0) (firstCurve d initial t)) ∧
      InRectangle (endpointBox d 0) (firstCurve d initial stepSize) ∧
      InRectangle (initialBox d 1) (firstCurve d initial stepSize) :=
  Classical.choose_spec (actual_first_step d initial.val initial.property)

def firstTarget (d : Direction) (initial : InitialAt d) : TargetAt d :=
  ⟨firstCurve d initial stepSize, (firstCurve_spec d initial).2.2.2⟩

def bandInitial (d : Direction) (p : {p : Point // p ∈ fullDomain}) : InitialAt d :=
  ⟨initialMap 0 4 p.val, actual_seed_initial d p.val p.property⟩

def cornerInitial (d : Direction) : InitialAt d :=
  bandInitial d ⟨fullLower, source_corner_inside⟩

theorem firstTarget_generated (d : Direction) (initial : InitialAt d) :
    (firstTarget d initial).val = firstCurve d initial stepSize := rfl

theorem firstCurve_continuousOn (d : Direction) (initial : InitialAt d) :
    ContinuousOn (firstCurve d initial) (Icc 0 (stepSize : ℝ)) :=
  HasDerivWithinAt.continuousOn (fun t ht => ((firstCurve_spec d initial).2.1 t ht).1)

theorem firstCurve_same_finite_initial (d : Direction) (p : {p : Point // p ∈ fullDomain}) :
    firstCurve d (bandInitial d p) 0 =
      TrueTubeError.finiteTrajectory (TrueTubeError.zeroTimeParameters p.val) 0 := by
  rw [(firstCurve_spec d _).1, TrueTubeError.finiteTrajectory_same_initial]
  rfl

structure FirstContinuationClosure : Prop where
  fields : type_of% TrueTubeMatrix.sourceGeneratedInitialTubeFields
  joins : type_of% complete_source_joins
  sourceInitial : type_of% actual_seed_initial
  actualFlow : type_of% firstCurve_spec
  targetGenerated : type_of% firstTarget_generated
  continuous : type_of% firstCurve_continuousOn
  finiteInitial : type_of% firstCurve_same_finite_initial
  finiteDefect : type_of% TrueTubeError.actual_defect_norm_le

theorem sourceGeneratedFirstContinuationClosure : FirstContinuationClosure where
  fields := TrueTubeMatrix.sourceGeneratedInitialTubeFields
  joins := complete_source_joins
  sourceInitial := actual_seed_initial
  actualFlow := firstCurve_spec
  targetGenerated := firstTarget_generated
  continuous := firstCurve_continuousOn
  finiteInitial := firstCurve_same_finite_initial
  finiteDefect := TrueTubeError.actual_defect_norm_le

end
end LAlanine40K2025.BasinRefinement.TrueTubeActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
