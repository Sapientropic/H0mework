import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Price
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
local notation "b" => burnolRieszSingleFourierSource
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "q" => (1/4:ℝ)

theorem source_cp_window (coordinate : BurnolCompletedMellinCoordinate)
    (h scale leg : ℝ) (nonnegative : 0≤h) :
    cotestColumn scale (pBand coordinate h leg)=
      cotestColumn scale (pGapBand coordinate h leg)-
        ((Real.exp (-leg/2):ℂ)/2) • windowKernelColumn (b coordinate) h scale leg := by
  have split : pBand coordinate h leg=pGapBand coordinate h leg-sourceFourierBand (b coordinate) h leg := by
    unfold pGapBand
    module
  rw [split,cotestColumn_sub,source_cotest_window_sandwich (b coordinate)
    (burnolRieszSingleFourierSource_reflection_fixed coordinate) h scale leg nonnegative]

def betaInventoryPrice (coordinate : BurnolCompletedMellinCoordinate) (h scale leg : ℝ) : ℂ :=
  -coupling coordinate*inner ℂ (b coordinate) (cotestColumn scale (pGapBand coordinate h leg))-
  star (Kernel.A coordinate)*inner ℂ Response.u (cotestColumn scale (pBand coordinate h leg))+
  star (Kernel.beta coordinate)*inner ℂ Response.u (cotestColumn scale (bBand coordinate h leg))-
  inner ℂ (b coordinate) (bandEndpoint h scale (pLeg coordinate leg))+
  inner ℂ (b coordinate) (forcePColumn coordinate h scale leg)+
  star (Kernel.beta coordinate)*(q:ℂ)*
    (pCotestRaw coordinate h scale leg q+pCotestRaw coordinate h scale leg (-q))

theorem beta_price_window (coordinate : BurnolCompletedMellinCoordinate)
    (h scale leg : ℝ) (nonnegative : 0≤h) :
    betaForcingPrice coordinate h scale leg=
      coupling coordinate*((Real.exp (-leg/2):ℂ)/2)*
        inner ℂ (b coordinate) (windowKernelColumn (b coordinate) h scale leg)+
      betaInventoryPrice coordinate h scale leg := by
  have source:=congrArg (fun z:BurnolQuarterMeanZeroCarrier=>inner ℂ (b coordinate) z)
    (source_cp_window coordinate h scale leg nonnegative)
  rw [inner_sub_right,inner_smul_right (b coordinate)
    (windowKernelColumn (b coordinate) h scale leg) ((Real.exp (-leg/2):ℂ)/2)] at source
  unfold betaForcingPrice betaInventoryPrice
  linear_combination -coupling coordinate*source

private theorem exp_pair (a : ℝ) : (Real.exp a:ℂ)*(Real.exp (-a):ℂ)=1 := by
  rw [← Complex.ofReal_mul,← Real.exp_add,add_neg_cancel,Real.exp_zero,Complex.ofReal_one]

def betaJointInventory (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  (Real.exp (h/4):ℂ)*betaInventoryPrice coordinate h (-h/2) (h/2)+
    (Real.exp (-h/4):ℂ)*betaInventoryPrice coordinate h (h/2) (-h/2)
def jointReactionPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  FixedWindowFourierReaction.mixedReactionPrice coordinate (upperRadius h)-
    FixedWindowFourierReaction.mixedReactionPrice coordinate (lowerRadius h)+
    originalJointWindowMeanPrice coordinate h

theorem beta_joint_window_price (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    (Real.exp (h/4):ℂ)*betaForcingPrice coordinate h (-h/2) (h/2)+
      (Real.exp (-h/4):ℂ)*betaForcingPrice coordinate h (h/2) (-h/2)=
      (coupling coordinate/2)*jointReactionPrice coordinate h+betaJointInventory coordinate h := by
  have paid:=original_joint_window_reaction_price coordinate h
  unfold FixedWindowFourierReaction.originalB at paid
  rw [← map_add,FixedWindowFourierReaction.quarterChart.inner_map_map] at paid
  change inner ℂ (b coordinate)
    (windowKernelColumn (b coordinate) h (-h/2) (h/2)+
      windowKernelColumn (b coordinate) h (h/2) (-h/2))=jointReactionPrice coordinate h at paid
  rw [inner_add_right] at paid
  have lower:=beta_price_window coordinate h (-h/2) (h/2) nonnegative
  have upper:=beta_price_window coordinate h (h/2) (-h/2) nonnegative
  have lowerUnit : (Real.exp (h/4):ℂ)*(Real.exp (-(h/2)/2):ℂ)=1 := by
    rw [show -(h/2)/2=-(h/4) by ring]
    exact exp_pair (h/4)
  have upperUnit : (Real.exp (-h/4):ℂ)*(Real.exp (-(-h/2)/2):ℂ)=1 := by
    rw [show -(-h/2)/2=-(-h/4) by ring]
    exact exp_pair (-h/4)
  unfold betaJointInventory
  rw [lower,upper]
  calc
    _=(coupling coordinate/2)*
      (inner ℂ (b coordinate) (windowKernelColumn (b coordinate) h (-h/2) (h/2))+
       inner ℂ (b coordinate) (windowKernelColumn (b coordinate) h (h/2) (-h/2)))+
      (Real.exp (h/4):ℂ)*betaInventoryPrice coordinate h (-h/2) (h/2)+
      (Real.exp (-h/4):ℂ)*betaInventoryPrice coordinate h (h/2) (-h/2) := by
      linear_combination coupling coordinate/2*
        inner ℂ (b coordinate) (windowKernelColumn (b coordinate) h (-h/2) (h/2))*lowerUnit+
        coupling coordinate/2*
        inner ℂ (b coordinate) (windowKernelColumn (b coordinate) h (h/2) (-h/2))*upperUnit
    _=_ := by rw [paid]; ring

def betaSkewInventory (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  (Real.exp (-h/4):ℂ)*(star (betaForcingPrice coordinate h (h/2) (-h/2))-
    betaForcingPrice coordinate h (h/2) (-h/2))
def completeBetaPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  (coupling coordinate/2)*jointReactionPrice coordinate h+
    betaJointInventory coordinate h+betaSkewInventory coordinate h

theorem actual_complete_beta_price (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    (Real.exp (h/4):ℂ)*star (Kernel.beta coordinate)*inner ℂ Response.eta (inverseCotest coordinate h).1+
      (Real.exp (-h/4):ℂ)*Kernel.beta coordinate*star (inner ℂ Response.eta (inverseCotest coordinate h).2)=
      completeBetaPrice coordinate h := by
  obtain ⟨lower,upper⟩:=actual_beta_forcing_read coordinate h nonnegative
  have reflected:=congrArg (starRingEnd ℂ) upper
  change star (star (Kernel.beta coordinate)*inner ℂ Response.eta (inverseCotest coordinate h).2)=
    star (betaForcingPrice coordinate h (h/2) (-h/2)) at reflected
  rw [star_mul,star_star] at reflected
  have full : (Real.exp (h/4):ℂ)*star (Kernel.beta coordinate)*inner ℂ Response.eta (inverseCotest coordinate h).1+
      (Real.exp (-h/4):ℂ)*Kernel.beta coordinate*star (inner ℂ Response.eta (inverseCotest coordinate h).2)=
      (Real.exp (h/4):ℂ)*betaForcingPrice coordinate h (-h/2) (h/2)+
      (Real.exp (-h/4):ℂ)*star (betaForcingPrice coordinate h (h/2) (-h/2)) := by
    linear_combination (Real.exp (h/4):ℂ)*lower+(Real.exp (-h/4):ℂ)*reflected
  rw [full]
  have joint:=beta_joint_window_price coordinate h nonnegative
  unfold completeBetaPrice betaSkewInventory
  linear_combination joint

end OriginalCommonInverseForcing.InverseEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
