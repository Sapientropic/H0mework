import H0mework.Physics.LowEnergy.FullQuantum.HistoryPrepared.Packet
import H0mework.Physics.YangMillsFlatQuantum.PairingOrigin
import H0mework.Physics.LowEnergyMatterSpace.SpatialCARNative

/-! Complete spatial operators and complete CAR words return through the original Stage10 preparation, after their full action. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryPrepared
open FullSpace YangMills.FullPairing Stage9DEF MatterSpace.SpatialCAR
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
noncomputable section

def sourceMother (A : FullMatterL2 →L[ℂ] FullMatterL2) : Mother :=
  fromOperator (preparation.adjoint.comp (A.comp preparation))

theorem sourceMother_read (A : FullMatterL2 →L[ℂ] FullMatterL2) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0) (Compatibility.responseMatrix (sourceMother A))=
      inner ℂ preparedPacket (A preparedPacket) := by
  rw [sourceMother,origin_response,operator_fromOperator]
  change inner ℂ (prepared 0) (preparation.adjoint (A (preparation (prepared 0))))=_
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem sourceMother_fullWord {ι : Type*} [Fintype ι] (tests : ι → FullMatterL2)
    (word : List (Letter (Option ι))) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (sourceMother (wordObservable preparedPacket tests word)))=
      spatialMoment preparedPacket tests word := by
  rw [sourceMother_read]
  exact wordObservable_response preparedPacket tests word

def originalMatterPacket : FullMatterL2 := preparation (naturalCoordinates (actual.matter 0))

theorem originalMatterPacket_amplitude : originalMatterPacket=(2 : ℂ) • preparedPacket := by
  rw [originalMatterPacket,actual_eq_twice_prepared,map_smul]
  rfl

theorem originalDual_initial (test : Hilbert) :
    actual.conjugateMatter 0 (naturalCoordinates.symm test)=
      inner ℂ ((2*(spinScale : ℂ)) • prepared 0) test := by
  rw [dual_origin,naturalCoordinates.apply_symm_apply,inner_smul_left]
  rw [map_mul,map_ofNat,Complex.conj_ofReal]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryPrepared
