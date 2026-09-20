import H0mework.Physics.MotherLaws.CurrentLinear

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentSampleAction

open StageNineSourceGeneratedMotherTimeCauchyFlow StageNineCanonicalCauchyState
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource StageNineHolonomicField
open SU7MotherLieAlgebra DiracExteriorMatterAction
open scoped ContDiff

noncomputable section

local instance smoothP286ModuleFinite : Module.Finite ℝ P286LieBlockData := ActualInitial.p286ModuleFinite
local instance smoothP286CoordinateFintype : Fintype P286CoordinateIndex := ActualInitial.p286CoordinateFintype
local instance smoothMatterCoordinateFintype : Fintype MatterCoordinateIndex := Fintype.ofFinite _

/-- The original mother-time transport preserves complete instantaneous
smoothness, including scalar velocity and the independently transported dual. -/
theorem mother_time_preserves_smooth (source : SmoothUnifiedSource) (time : ℝ)
    (initial : StageNineCauchyState) (smooth : ActualInitial.SmoothInitial initial) :
    ActualInitial.SmoothInitial (sourceGeneratedMotherTimeCauchyUpdate source time initial) := by
  let gauge : P286CoordinateCarrier →L[ℝ] P286CoordinateCarrier :=
    ⟨gaugeCoordinates source time, gauge_continuous source time⟩
  let scalar : ScalarCoordinateCarrier →L[ℝ] ScalarCoordinateCarrier :=
    ⟨(scalarCoordinates source time).restrictScalars ℝ, scalar_continuous source time⟩
  let matter : MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
    ⟨(matterCoordinates source time).restrictScalars ℝ, matter_continuous source time⟩
  let dual : (MatterCoordinateIndex → ℂ) →L[ℝ] (MatterCoordinateIndex → ℂ) :=
    ⟨(dualCoordinates source time).restrictScalars ℝ, dual_continuous source time⟩
  refine ⟨smooth.coframe, smooth.gravityConnection, smooth.gravityAuxiliary,
    smooth.gravitySimplicityMultiplier, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro direction
    have transformed := gauge.contDiff.comp (smooth.gaugeConnection direction)
    change ContDiff ℝ ∞ (fun space => gaugeCoordinates source time
      (p286CoordinateEquiv (initial.gaugeConnection space direction))) at transformed
    simpa only [gauge_coordinates_actual, sourceGeneratedMotherTimeCauchyUpdate] using transformed
  · intro pair
    have transformed := gauge.contDiff.comp (smooth.gaugeAuxiliary pair)
    change ContDiff ℝ ∞ (fun space => gaugeCoordinates source time
      (p286CoordinateEquiv (initial.gaugeAuxiliary space pair))) at transformed
    simpa only [gauge_coordinates_actual, sourceGeneratedMotherTimeCauchyUpdate] using transformed
  · have transformed := scalar.contDiff.comp smooth.scalar
    change ContDiff ℝ ∞ (fun space => scalarCoordinates source time (initial.scalar space)) at transformed
    simpa only [scalar_coordinates_actual, sourceGeneratedMotherTimeCauchyUpdate] using transformed
  · have transformed := scalar.contDiff.comp smooth.scalarVelocity
    change ContDiff ℝ ∞ (fun space => scalarCoordinates source time (initial.scalarVelocity space)) at transformed
    simpa only [scalar_coordinates_actual, sourceGeneratedMotherTimeCauchyUpdate] using transformed
  · have transformed := matter.contDiff.comp smooth.matter
    change ContDiff ℝ ∞ (fun space => matterCoordinates source time
      (matterCoordinateEquiv (initial.matter space))) at transformed
    simpa only [matter_coordinates_actual, sourceGeneratedMotherTimeCauchyUpdate] using transformed
  · intro index
    have initialDual : ContDiff ℝ ∞ (fun space => fun coordinate : MatterCoordinateIndex =>
        initial.conjugateMatter space (matterCoordinateEquiv.symm (EuclideanSpace.single coordinate 1))) :=
      contDiff_pi.2 smooth.conjugateMatter
    have transformed := dual.contDiff.comp initialDual
    change ContDiff ℝ ∞ (fun space => dualCoordinates source time
      (fun coordinate => initial.conjugateMatter space
        (matterCoordinateEquiv.symm (EuclideanSpace.single coordinate 1)))) at transformed
    simp_rw [dual_coordinates_actual] at transformed
    exact (contDiff_pi.1 transformed) index

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentSampleAction
