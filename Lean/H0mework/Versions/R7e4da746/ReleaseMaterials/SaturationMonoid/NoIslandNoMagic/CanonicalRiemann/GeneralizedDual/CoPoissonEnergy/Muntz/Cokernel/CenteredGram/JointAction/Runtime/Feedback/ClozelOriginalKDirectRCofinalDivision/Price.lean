import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalTwoDirection.Physical

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
local instance priceComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
namespace K
export OriginalKCombCofinalTwoDirection (originalK originalFourierK)
end K
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def sourceReturn : BurnolPaAmbientCarrier :=
 PA.Q (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)))

private theorem actual_Q_read (probe : BurnolL2) :
 inner ℂ probe (PA.Q (D.raw observation nontrivial half depth (ordinal+1)) : BurnolL2)=
 sourceCoefficient observation nontrivial half depth ordinal *
  inner ℂ probe (sourceUnit observation nontrivial half : BurnolL2)+
 inner ℂ probe (sourceReturn observation nontrivial half depth ordinal : BurnolL2) := by
 rw [actual_Q_successor]
 change inner ℂ probe
  (sourceCoefficient observation nontrivial half depth ordinal •
   (sourceUnit observation nontrivial half : BurnolL2)+
   (sourceReturn observation nontrivial half depth ordinal : BurnolL2))=_
 rw [inner_add_right,inner_smul_right]

theorem actual_original_K_read :
 inner ℂ (K.originalK observation nontrivial half)
  (PA.Q (D.raw observation nontrivial half depth (ordinal+1)) : BurnolL2)=
 sourceCoefficient observation nontrivial half depth ordinal *
  inner ℂ (K.originalK observation nontrivial half) (sourceUnit observation nontrivial half : BurnolL2)+
 inner ℂ (K.originalK observation nontrivial half)
  (sourceReturn observation nontrivial half depth ordinal : BurnolL2) :=
 actual_Q_read observation nontrivial half depth ordinal (K.originalK observation nontrivial half)

theorem actual_original_FourierK_read :
 inner ℂ (K.originalFourierK observation nontrivial half)
  (PA.Q (D.raw observation nontrivial half depth (ordinal+1)) : BurnolL2)=
 sourceCoefficient observation nontrivial half depth ordinal *
  inner ℂ (K.originalFourierK observation nontrivial half) (sourceUnit observation nontrivial half : BurnolL2)+
 inner ℂ (K.originalFourierK observation nontrivial half)
  (sourceReturn observation nontrivial half depth ordinal : BurnolL2) :=
 actual_Q_read observation nontrivial half depth ordinal (K.originalFourierK observation nontrivial half)

theorem actual_Q_complete_gram :
 ‖PA.Q (D.raw observation nontrivial half depth (ordinal+1))‖^2=
 ‖sourceCoefficient observation nontrivial half depth ordinal‖^2 * ‖sourceUnit observation nontrivial half‖^2+
  2*(inner ℂ (sourceCoefficient observation nontrivial half depth ordinal • sourceUnit observation nontrivial half)
   (sourceReturn observation nontrivial half depth ordinal)).re+
  ‖sourceReturn observation nontrivial half depth ordinal‖^2 := by
 change ‖PA.Q (D.raw observation nontrivial half depth (ordinal+1))‖^2=
  ‖sourceCoefficient observation nontrivial half depth ordinal‖^2 * ‖sourceUnit observation nontrivial half‖^2+
   2*(inner ℂ (sourceCoefficient observation nontrivial half depth ordinal • sourceUnit observation nontrivial half)
    (PA.Q (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal))))).re+
   ‖PA.Q (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)))‖^2
 rw [actual_Q_successor,norm_add_sq (𝕜:=ℂ),norm_smul,mul_pow]
 simp only [RCLike.re_to_complex]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
