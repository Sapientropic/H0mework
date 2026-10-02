import H0mework.Versions.R2.Physics.MotherLaws.CurrentLinear

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentSampleAction

open CurrentMaterial StageNineCanonicalCauchyState StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource

noncomputable section

local instance : Module.Finite ℝ SU7MotherLieAlgebra.P286LieBlockData := ActualInitial.p286ModuleFinite
local instance : Fintype P286CoordinateIndex := ActualInitial.p286CoordinateFintype
local instance : Fintype MatterCoordinateIndex := Fintype.ofFinite _

def realSample (samples : ℕ → ℝ) (point : RationalPoint) (channel : Channel) : ℝ :=
  samples (Encodable.encode (point, channel))

def complexSample (samples : ℕ → ℝ) (point : RationalPoint) (channel : Bool → Channel) : ℂ :=
  ⟨realSample samples point (channel false), realSample samples point (channel true)⟩

/-- The original source action acts on all channels at this same spatial sample. -/
def channelUpdate (source : SmoothUnifiedSource) (time : ℝ) (samples : ℕ → ℝ)
    (point : RationalPoint) : Channel → ℝ
  | .coframe row column => realSample samples point (.coframe row column)
  | .gravityConnection direction row column => realSample samples point (.gravityConnection direction row column)
  | .gravityAuxiliary internalPair spacetimePair => realSample samples point (.gravityAuxiliary internalPair spacetimePair)
  | .gravityMultiplier internalPair spacetimePair => realSample samples point (.gravityMultiplier internalPair spacetimePair)
  | .gaugeConnection direction coordinate =>
      gaugeCoordinates source time
        (WithLp.toLp 2 (fun index => realSample samples point (.gaugeConnection direction index))) coordinate
  | .gaugeAuxiliary pair coordinate =>
      gaugeCoordinates source time
        (WithLp.toLp 2 (fun index => realSample samples point (.gaugeAuxiliary pair index))) coordinate
  | .scalar coordinate imaginary => complexPart imaginary
      (scalarCoordinates source time
        (WithLp.toLp 2 (fun index => complexSample samples point (.scalar index))) coordinate)
  | .scalarVelocity coordinate imaginary => complexPart imaginary
      (scalarCoordinates source time
        (WithLp.toLp 2 (fun index => complexSample samples point (.scalarVelocity index))) coordinate)
  | .matter coordinate imaginary => complexPart imaginary
      (matterCoordinates source time
        (WithLp.toLp 2 (fun index => complexSample samples point (.matter index))) coordinate)
  | .dual coordinate imaginary => complexPart imaginary
      (dualCoordinates source time (fun index => complexSample samples point (.dual index)) coordinate)
  | .clock => realSample samples point .clock + time

def updateSamples (source : SmoothUnifiedSource) (time : ℝ) (samples : ℕ → ℝ) : ℕ → ℝ :=
  fun address => match Encodable.decode (α := Query) address with
    | none => 0
    | some query => channelUpdate source time samples query.1 query.2

theorem realSample_actual (initial : StageNineCauchyState) (clock : ℝ)
    (point : RationalPoint) (channel : Channel) :
    realSample (currentSamples initial clock) point channel =
      observe initial clock channel (rationalPoint point) := by
  simp only [realSample, currentSamples, Encodable.encodek]

theorem complexSample_actual (initial : StageNineCauchyState) (clock : ℝ)
    (point : RationalPoint) (channel : Bool → Channel) (value : ℂ)
    (real_part : observe initial clock (channel false) (rationalPoint point) = value.re)
    (imag_part : observe initial clock (channel true) (rationalPoint point) = value.im) :
    complexSample (currentSamples initial clock) point channel = value := by
  simp only [complexSample, realSample_actual, real_part, imag_part]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentSampleAction
