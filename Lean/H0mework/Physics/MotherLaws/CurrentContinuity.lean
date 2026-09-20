import H0mework.Physics.MotherLaws.CurrentSamples

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentSampleAction

open CurrentMaterial StageNineHolonomicField StageNineEnrichedProofFreeSource

noncomputable section

local instance : Module.Finite ℝ SU7MotherLieAlgebra.P286LieBlockData := ActualInitial.p286ModuleFinite
local instance : Fintype P286CoordinateIndex := ActualInitial.p286CoordinateFintype
local instance : Fintype MatterCoordinateIndex := Fintype.ofFinite _

theorem complexSample_continuous (point : RationalPoint) (channel : Bool → Channel) :
    Continuous (fun samples => complexSample samples point channel) := by
  simp only [complexSample, Complex.mk_eq_add_mul_I]
  exact (Complex.continuous_ofReal.comp (continuous_apply _)).add
    ((Complex.continuous_ofReal.comp (continuous_apply _)).mul_const Complex.I)

theorem realInputs_continuous {ι : Type*} [Fintype ι]
    (point : RationalPoint) (channels : ι → Channel) :
    Continuous (fun samples : ℕ → ℝ =>
      WithLp.toLp 2 (fun index => realSample samples point (channels index))) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_apply _)

theorem complexInputs_continuous {ι : Type*} [Fintype ι]
    (point : RationalPoint) (channels : ι → Bool → Channel) :
    Continuous (fun samples : ℕ → ℝ =>
      WithLp.toLp 2 (fun index => complexSample samples point (channels index))) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => complexSample_continuous _ _)

theorem channelUpdate_continuous (source : SmoothUnifiedSource) (time : ℝ)
    (point : RationalPoint) (channel : Channel) :
    Continuous (fun samples => channelUpdate source time samples point channel) := by
  cases channel with
  | coframe row column => exact continuous_apply _
  | gravityConnection direction row column => exact continuous_apply _
  | gravityAuxiliary internalPair spacetimePair => exact continuous_apply _
  | gravityMultiplier internalPair spacetimePair => exact continuous_apply _
  | gaugeConnection direction coordinate =>
      exact (PiLp.continuous_apply 2 _ coordinate).comp
        ((gauge_continuous source time).comp (realInputs_continuous point _))
  | gaugeAuxiliary pair coordinate =>
      exact (PiLp.continuous_apply 2 _ coordinate).comp
        ((gauge_continuous source time).comp (realInputs_continuous point _))
  | scalar coordinate imaginary =>
      exact (complexPart_continuous imaginary).comp
        ((PiLp.continuous_apply 2 _ coordinate).comp
          ((scalar_continuous source time).comp (complexInputs_continuous point _)))
  | scalarVelocity coordinate imaginary =>
      exact (complexPart_continuous imaginary).comp
        ((PiLp.continuous_apply 2 _ coordinate).comp
          ((scalar_continuous source time).comp (complexInputs_continuous point _)))
  | matter coordinate imaginary =>
      exact (complexPart_continuous imaginary).comp
        ((PiLp.continuous_apply 2 _ coordinate).comp
          ((matter_continuous source time).comp (complexInputs_continuous point _)))
  | dual coordinate imaginary =>
      exact (complexPart_continuous imaginary).comp
        ((continuous_apply coordinate).comp
          ((dual_continuous source time).comp
            (continuous_pi fun _ => complexSample_continuous point _)))
  | clock =>
      change Continuous (fun samples : ℕ → ℝ => realSample samples point .clock + time)
      exact (continuous_apply _).add continuous_const

theorem updateSamples_continuous (source : SmoothUnifiedSource) (time : ℝ) :
    Continuous (updateSamples source time) := by
  apply continuous_pi
  intro address
  unfold updateSamples
  cases Encodable.decode (α := Query) address with
  | none => exact continuous_const
  | some query => exact channelUpdate_continuous source time query.1 query.2

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentSampleAction
