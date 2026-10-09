import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation.Spatial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation.Trajectory

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient
noncomputable section
variable (current : Material)

def travel (phase : Phase) (t : ℝ) : ℝ := shift current phase t (0,0)
def travelRate (phase : Phase) (t : ℝ) : ℝ := shiftRate current phase t (0,0)
def movingPoint (phase : Phase) (t : ℝ) (x : Point) : Point :=
  Function.update (x-translationPoint current) 0 (x 0-travel current phase t)
def movingJet (i : Basis) (jet : MultiIndex) (phase : Phase) (t : ℝ) (x : Point) : ℝ :=
  orbital (sourceTerms i) jet (movingPoint current phase t x)

theorem moving_point_source (x : Point) : movingPoint current .enter 0 x=x-translationPoint current := by
  unfold movingPoint travel shift
  exact Function.update_eq_self _ _

theorem moving_point_target (x : Point) : movingPoint current .leave duration x=x-translationPoint (nextMaterial current) := by
  funext k
  by_cases same : k=0
  · subst k
    simp only [movingPoint,travel,shift,Function.update_self,Pi.sub_apply,translationPoint,
      next_offset,Rat.cast_add]
  · simp only [movingPoint,Function.update_of_ne same,Pi.sub_apply,translationPoint,
      next_offset,increment,SpatialActuation.axisQ,if_neg same,mul_zero,add_zero]

theorem moving_jet_source (i : Basis) (jet : MultiIndex) (x : Point) :
    movingJet current i jet .enter 0 x=aoJet current i jet x := by
  rw [movingJet,moving_point_source,ao_jet_translation]

theorem moving_jet_target (i : Basis) (jet : MultiIndex) (x : Point) :
    movingJet current i jet .leave duration x=aoJet (nextMaterial current) i jet x := by
  rw [movingJet,moving_point_target,ao_jet_translation]

theorem moving_point_junctions (x : Point) :
    movingPoint current .enter duration x=movingPoint current .drive 0 x ∧
    movingPoint current .drive duration x=movingPoint current .leave 0 x := by
  unfold movingPoint travel
  rw [(shift_junctions current).1,(shift_junctions current).2.1]
  exact ⟨rfl,rfl⟩

theorem moving_jet_derivative (i : Basis) (jet : MultiIndex) (phase : Phase) (t : ℝ) (x : Point) :
    HasDerivAt (fun time => movingJet current i jet phase time x)
      (-travelRate current phase t*movingJet current i (raise jet 0) phase t x) t := by
  have motion : HasDerivAt (fun time => x 0-travel current phase time) (-travelRate current phase t) t := by
    simpa only [travel,travelRate,zero_sub] using!
      (hasDerivAt_const t (x 0)).sub (shift_derivative current phase t (0,0))
  have original := orbital_coordinate_derivative (sourceTerms i) jet (movingPoint current phase t x) 0
  have composed := original.comp t motion
  simpa [movingJet,movingPoint,Function.comp_def,mul_comm] using! composed

theorem moving_jet_continuous (i : Basis) (jet : MultiIndex) (phase : Phase) (x : Point) :
    Continuous (fun t => movingJet current i jet phase t x) :=
  continuous_iff_continuousAt.mpr fun t => (moving_jet_derivative current i jet phase t x).continuousAt

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation
