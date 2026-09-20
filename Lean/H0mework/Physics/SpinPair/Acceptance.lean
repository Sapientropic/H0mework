import H0mework.Physics.SpinPair.Coframe
import H0mework.Physics.SpinPair.AdjointActual
import H0mework.Physics.SpinPair.Qualification

/-! The original six-field S9-C key, generated on one source actual.
The nine Euler channels hold at every spacetime point. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open StageNineEnrichedProofFreeSource StageNineCClassicalWorldAcceptance
open StageNineDiracDualFormNativeJointResidualCarrier Stage9C.Reduction

noncomputable section

theorem actual_jointZeroFiber :
    DiracDualFormNativeJointZeroFiber positiveSmoothUnifiedSource actual := by
  apply (algebraicCartanReduction_jointZero_iff positiveSmoothUnifiedSource seed
    seed_smooth seed_nondegenerate).2
  intro point
  exact ⟨actual_gaugeEuler_zero point,
    funext (actual_scalarEuler_zero point),
    funext (actual_matterEuler_zero point),
    funext (actual_conjugateMatterEuler_zero point),
    actual_coframeEuler_zero point⟩

theorem actual_classicalWorldAcceptance :
    ClassicalWorldAcceptance positiveSmoothUnifiedSource actual where
  smooth := actual_smooth
  nondegenerate := actual_nondegenerate
  gravityConnectionLorentzAdmissible := actual_lorentzAdmissible
  jointZeroFiber := actual_jointZeroFiber
  dynamicScalarSourceContact := actual_dynamicScalarSourceContact
  simultaneousSixPhysicalSectorNonzero := actual_sixPhysicalSectors

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
