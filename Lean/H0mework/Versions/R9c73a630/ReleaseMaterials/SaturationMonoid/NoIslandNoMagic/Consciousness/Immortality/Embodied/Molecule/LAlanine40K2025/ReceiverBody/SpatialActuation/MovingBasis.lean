import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Spatial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Trajectory

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient
noncomputable section

def travel (phase : Phase) (t : ℝ) : ℝ := shift phase t (0,0)
def travelRate (phase : Phase) (t : ℝ) : ℝ := shiftRate phase t (0,0)
def movingPoint (phase : Phase) (t : ℝ) (x : Point) : Point :=
  Function.update x 0 (x 0-travel phase t)
def movingJet (i : Basis) (jet : MultiIndex) (phase : Phase) (t : ℝ) (x : Point) : ℝ :=
  orbital (sourceTerms i) jet (movingPoint phase t x)

theorem moving_point_source (x : Point) : movingPoint .enter 0 x=x := by
  simp only [movingPoint,travel,shift,sub_zero,Function.update_eq_self]

theorem moving_point_target (x : Point) : movingPoint .leave duration x=x-offset := by
  funext k
  by_cases same : k=0
  · subst k
    simp [movingPoint,travel,shift,displacement,axisQ,offset,offsetQ]
  · simp only [movingPoint,Function.update_of_ne same,Pi.sub_apply,offset,offsetQ,axisQ,
      if_neg same,mul_zero,Rat.cast_zero,sub_zero]

theorem moving_jet_source (i : Basis) (jet : MultiIndex) (x : Point) :
    movingJet i jet .enter 0 x=orbital (sourceTerms i) jet x := by
  rw [movingJet,moving_point_source]

theorem moving_jet_target (i : Basis) (jet : MultiIndex) (x : Point) :
    movingJet i jet .leave duration x=aoJet i jet x := by
  rw [movingJet,moving_point_target,ao_jet_translation]

theorem moving_point_junctions (x : Point) :
    movingPoint .enter duration x=movingPoint .drive 0 x ∧
    movingPoint .drive duration x=movingPoint .leave 0 x := by
  unfold movingPoint travel
  rw [shift_junctions.1,shift_junctions.2.1]
  exact ⟨rfl,rfl⟩

theorem moving_jet_derivative (i : Basis) (jet : MultiIndex) (phase : Phase) (t : ℝ) (x : Point) :
    HasDerivAt (fun time => movingJet i jet phase time x)
      (-travelRate phase t*movingJet i (raise jet 0) phase t x) t := by
  have motion : HasDerivAt (fun time => x 0-travel phase time) (-travelRate phase t) t := by
    simpa only [travel,travelRate,zero_sub] using!
      (hasDerivAt_const t (x 0)).sub (shift_derivative phase t (0,0))
  have original := orbital_coordinate_derivative (sourceTerms i) jet (movingPoint phase t x) 0
  have composed := original.comp t motion
  simpa [movingJet,movingPoint,Function.comp_def,mul_comm] using! composed

theorem moving_jet_continuous (i : Basis) (jet : MultiIndex) (phase : Phase) (x : Point) :
    Continuous (fun t => movingJet i jet phase t x) :=
  continuous_iff_continuousAt.mpr fun t => (moving_jet_derivative i jet phase t x).continuousAt

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
