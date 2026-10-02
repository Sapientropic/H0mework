import H0mework.Versions.R2.Physics.MotherLaws.CurrentContinuity

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentSampleAction

open CurrentMaterial StageNineCanonicalCauchyState StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open StageNineSourceGeneratedMotherTimeCauchyFlow

noncomputable section

local instance : Module.Finite ℝ SU7MotherLieAlgebra.P286LieBlockData := ActualInitial.p286ModuleFinite
local instance : Fintype P286CoordinateIndex := ActualInitial.p286CoordinateFintype
local instance : Fintype MatterCoordinateIndex := Fintype.ofFinite _

theorem channelUpdate_actual (source : SmoothUnifiedSource) (time : ℝ)
    (initial : StageNineCauchyState) (clock : ℝ) (point : RationalPoint) (channel : Channel) :
    channelUpdate source time (currentSamples initial clock) point channel =
      observe (sourceGeneratedMotherTimeCauchyUpdate source time initial) (clock + time)
        channel (rationalPoint point) := by
  cases channel with
  | coframe row column => exact realSample_actual initial clock point _
  | gravityConnection direction row column => exact realSample_actual initial clock point _
  | gravityAuxiliary internalPair spacetimePair => exact realSample_actual initial clock point _
  | gravityMultiplier internalPair spacetimePair => exact realSample_actual initial clock point _
  | gaugeConnection direction coordinate =>
      simpa only [channelUpdate, realSample_actual, observe, sourceGeneratedMotherTimeCauchyUpdate] using
        congrArg (fun value : P286CoordinateCarrier => value coordinate)
          (gauge_coordinates_actual source time (initial.gaugeConnection (rationalPoint point) direction))
  | gaugeAuxiliary pair coordinate =>
      simpa only [channelUpdate, realSample_actual, observe, sourceGeneratedMotherTimeCauchyUpdate] using
        congrArg (fun value : P286CoordinateCarrier => value coordinate)
          (gauge_coordinates_actual source time (initial.gaugeAuxiliary (rationalPoint point) pair))
  | scalar coordinate imaginary =>
      simpa [channelUpdate, complexSample, realSample_actual, observe, complexPart,
        sourceGeneratedMotherTimeCauchyUpdate] using
        congrArg (fun value : ScalarCoordinateCarrier => complexPart imaginary (value coordinate))
          (scalar_coordinates_actual source time (initial.scalar (rationalPoint point)))
  | scalarVelocity coordinate imaginary =>
      simpa [channelUpdate, complexSample, realSample_actual, observe, complexPart,
        sourceGeneratedMotherTimeCauchyUpdate] using
        congrArg (fun value : ScalarCoordinateCarrier => complexPart imaginary (value coordinate))
          (scalar_coordinates_actual source time (initial.scalarVelocity (rationalPoint point)))
  | matter coordinate imaginary =>
      simpa [channelUpdate, complexSample, realSample_actual, observe, complexPart,
        sourceGeneratedMotherTimeCauchyUpdate] using
        congrArg (fun value : MatterCoordinateCarrier => complexPart imaginary (value coordinate))
          (matter_coordinates_actual source time (initial.matter (rationalPoint point)))
  | dual coordinate imaginary =>
      simpa [channelUpdate, complexSample, realSample_actual, observe, complexPart,
        sourceGeneratedMotherTimeCauchyUpdate] using
        congrArg (fun value : MatterCoordinateIndex → ℂ => complexPart imaginary (value coordinate))
          (dual_coordinates_actual source time (initial.conjugateMatter (rationalPoint point)))
  | clock => exact congrArg (fun value : ℝ => value + time) (realSample_actual initial clock point .clock)

/-- The whole original physical action commutes with the fixed complete sample layout. -/
theorem updateSamples_actual (source : SmoothUnifiedSource) (time : ℝ)
    (initial : StageNineCauchyState) (clock : ℝ) :
    updateSamples source time (currentSamples initial clock) =
      currentSamples (sourceGeneratedMotherTimeCauchyUpdate source time initial) (clock + time) := by
  funext address
  unfold updateSamples currentSamples
  cases Encodable.decode (α := Query) address with
  | none => rfl
  | some query => exact channelUpdate_actual source time initial clock query.1 query.2

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentSampleAction
