import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Decomposition
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.InverseEuler
open Complex MeasureTheory OriginalRieszSource
open scoped InnerProductSpace
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing

def remainingAReturnRead (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  (Real.exp (h/4):ℂ)*star (Kernel.A coordinate)*inner ℂ Response.eta (inversePartner coordinate h).1+
    (Real.exp (-h/4):ℂ)*Kernel.A coordinate*star (inner ℂ Response.eta (inversePartner coordinate h).2)
def eulerReactionForcingRead (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  remainingAReturnRead coordinate h-completeBetaPrice coordinate h

theorem full_forcing_euler_reaction (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    (∫ x:ℝ in (lowerRadius h)..(upperRadius h),forcingCross coordinate h x)=
      eulerReactionForcingRead coordinate h+forcingInventory coordinate h := by
  have source:=forcingCross_common_inverse coordinate h nonnegative
  have beta:=actual_complete_beta_price coordinate h nonnegative
  have actual : inverseForcingRead coordinate h=eulerReactionForcingRead coordinate h := by
    unfold inverseForcingRead eulerReactionForcingRead remainingAReturnRead
    linear_combination -beta
  rw [source,actual]

def eulerReactionPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  2*(sourceAction coordinate h (upperRadius h)-sourceAction coordinate h (lowerRadius h)-
    eulerReactionForcingRead coordinate h-forcingInventory coordinate h)/coupling coordinate

theorem generated_euler_reaction_price (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) : eulerReactionPrice coordinate h=forcingPrice coordinate h := by
  unfold eulerReactionPrice forcingPrice
  rw [full_forcing_euler_reaction coordinate h nonnegative]
  ring

end OriginalCommonInverseForcing.InverseEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
