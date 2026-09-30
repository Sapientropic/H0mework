import H0mework.Physics.LowEnergy.PacketGaugeNoise.Noise
import H0mework.Physics.LowEnergy.FullQuantum.HistoryPrepared.Source

/-! The same normalized source state reads the complete CAR words. Every
current leg and its actual mean variation are composed before Stage10 readout. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketGaugeNoise
open FullQuantum FullSpace PacketNoise PacketFourier GaugeGreen HistoryPrepared Stage9DEF
open MatterSpace.SpatialCAR
noncomputable section

theorem preparedState_unit : ‖preparedState‖=1 := filteredPacket_unit 0 1 positiveDamping

theorem preparedState_pair : inner ℂ preparedState preparedState=1 :=
  inner_self_eq_one_of_norm_eq_one preparedState_unit

theorem variationVector_current (gauge : GaugeProfile) (shift : Position) :
    variationVector gauge shift=currentVariation gauge shift preparedState-
      meanVariation gauge shift • preparedState := rfl

theorem meanVariation_current (gauge : GaugeProfile) (shift : Position) :
    meanVariation gauge shift=inner ℂ preparedState (currentVariation gauge shift preparedState) := rfl

theorem variationVector_orthogonal (gauge : GaugeProfile) (shift : Position) :
    inner ℂ preparedState (variationVector gauge shift)=0 := by
  rw [variationVector_current,inner_sub_right,inner_smul_right,preparedState_pair,
    meanVariation_current,mul_one,sub_self]

theorem filteredWord_read {ι : Type*} [Fintype ι] (tests : ι → FullMatterL2)
    (word : List (Letter (Option ι))) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (filteredMother 0 1 positiveDamping
        (wordObservable preparedState tests word)))=spatialMoment preparedState tests word := by
  rw [filtered_source_read]
  exact wordObservable_response preparedState tests word

def familyTests (gauge : GaugeProfile) (epsilon : ℝ) (left right : Position) : Fin 2 → FullMatterL2 :=
  ![packetFamily gauge epsilon left,packetFamily gauge epsilon right]

def familyWord (gauge : GaugeProfile) (epsilon : ℝ) (left right : Position) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  wordObservable preparedState (familyTests gauge epsilon left right)
    [.create none,.annihilate (some 0),.create (some 1),.annihilate none]

theorem noiseFamily_source_word (gauge : GaugeProfile) (epsilon : ℝ) (left right : Position) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (filteredMother 0 1 positiveDamping
        (familyWord gauge epsilon left right)))=noiseFamily gauge epsilon left right := by
  rw [familyWord,filteredWord_read,spatialMoment_fourPoint]
  change inner ℂ (packetFamily gauge epsilon left) (packetFamily gauge epsilon right)*
    inner ℂ preparedState preparedState*inner ℂ preparedState preparedState=_
  rw [preparedState_pair,mul_one,mul_one]
  rfl

def slopeTests (gauge : GaugeProfile) (left right : Position) : Fin 4 → FullMatterL2 :=
  ![variationVector gauge left,phasePacket 0 1 positiveDamping right 0,
    phasePacket 0 1 positiveDamping left 0,variationVector gauge right]

def firstSlopeWord (gauge : GaugeProfile) (left right : Position) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  wordObservable preparedState (slopeTests gauge left right)
    [.create none,.annihilate (some 0),.create (some 1),.annihilate none]

def secondSlopeWord (gauge : GaugeProfile) (left right : Position) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  wordObservable preparedState (slopeTests gauge left right)
    [.create none,.annihilate (some 2),.create (some 3),.annihilate none]

def noiseStateSlope (gauge : GaugeProfile) (left right : Position) : ℂ :=
  State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
    (Compatibility.responseMatrix (filteredMother 0 1 positiveDamping (firstSlopeWord gauge left right)))+
  State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
    (Compatibility.responseMatrix (filteredMother 0 1 positiveDamping (secondSlopeWord gauge left right)))

theorem noiseStateSlope_original (gauge : GaugeProfile) (left right : Position) :
    noiseStateSlope gauge left right=noiseSlope gauge left right := by
  rw [noiseStateSlope,firstSlopeWord,secondSlopeWord,filteredWord_read,filteredWord_read,
    spatialMoment_fourPoint,spatialMoment_fourPoint]
  change (inner ℂ (variationVector gauge left) (phasePacket 0 1 positiveDamping right 0)*
      inner ℂ preparedState preparedState*inner ℂ preparedState preparedState)+
    (inner ℂ (phasePacket 0 1 positiveDamping left 0) (variationVector gauge right)*
      inner ℂ preparedState preparedState*inner ℂ preparedState preparedState)=_
  rw [preparedState_pair,mul_one,mul_one,mul_one,mul_one]
  rfl

theorem noiseFamily_state_derivative (gauge : GaugeProfile) (left right : Position) :
    HasDerivAt (fun epsilon => State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (filteredMother 0 1 positiveDamping
        (familyWord gauge epsilon left right)))) (noiseStateSlope gauge left right) 0 := by
  simpa only [noiseFamily_source_word,noiseStateSlope_original] using
    noiseFamily_derivative gauge left right

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketGaugeNoise
