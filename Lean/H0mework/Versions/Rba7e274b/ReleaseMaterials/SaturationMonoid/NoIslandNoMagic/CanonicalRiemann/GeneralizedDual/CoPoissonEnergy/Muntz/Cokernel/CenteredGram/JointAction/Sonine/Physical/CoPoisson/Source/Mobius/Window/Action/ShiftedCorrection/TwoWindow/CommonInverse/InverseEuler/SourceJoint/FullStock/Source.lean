import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.NativeJointAction

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.SourceJoint.FullStock
open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing.InverseEuler

/-- Every n>1 channel remains combined with its own native subtraction inside
its original whole-axis integral. The two original means keep their seed masses. -/
def nativeStock (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  (∫ x : ℝ,inner ℂ (Higher.higherCountingRaw (NativeWeight.bandLower h) 4
    (NativeWeight.positionWeight coordinate h) x) ((burnolCompletedMellinRieszVector coordinate:BurnolL2) x))+
  (∫ x : ℝ,inner ℂ (Higher.higherCountingRaw (NativeWeight.bandLower h) 4
    (NativeWeight.fourierWeight coordinate h) x) (fourierL2 (burnolCompletedMellinRieszVector coordinate:BurnolL2) x))+
  positionMean coordinate*star (∫ x : ℝ,Seed.positionSeed coordinate h x)+
  fourierMean coordinate*star (∫ x : ℝ,Seed.fourierSeed coordinate h x)

theorem actual_whole_correction_stock (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) : correctionRead coordinate h=nativeStock coordinate h := by
  unfold correctionRead nativeStock
  rw [Higher.position_correction_higher_pairing coordinate h nonnegative,
    Higher.fourier_correction_higher_pairing coordinate h nonnegative]

/-- The generated mean prices are retained beside the concrete higher-count
price; the exact source normalization is inherited, never guessed. -/
theorem actual_scaled_whole_stock (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) :
    star (upperSeedFactor h)*nativeStock coordinate h=upperHigherSourcePrice coordinate h+
      star (upperSeedFactor h)*(positionMean coordinate*star (∫ x : ℝ,Seed.positionSeed coordinate h x)+
        fourierMean coordinate*star (∫ x : ℝ,Seed.fourierSeed coordinate h x)) := by
  unfold nativeStock upperHigherSourcePrice
  ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

theorem actual_stock_complete_forcing (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    forcingPrice (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h=
      nativeStock (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h := by
  rw [← OriginalTwoWindowInverseForcing.original_correction_forcing_action_price observation nontrivial half h nonnegative bounded]
  exact actual_whole_correction_stock _ h nonnegative

theorem actual_stock_generated_forcing (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    (∫ x : ℝ in (lowerRadius h)..(upperRadius h),
      forcingCross (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h x)=
      sourceAction (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h (upperRadius h)-
      sourceAction (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h (lowerRadius h)-
      (coupling (OriginalJointFluxSource.Prior.coordinate observation nontrivial half)/2)*
        nativeStock (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h := by
  have computed:=actual_stock_complete_forcing observation nontrivial half h nonnegative bounded
  have nonzero:=OriginalRieszSourceGreen.source_cross_parameter_ne_zero
    (OriginalJointFluxSource.Prior.coordinate observation nontrivial half)
    (OriginalJointFluxSource.Prior.coordinate observation nontrivial half)
  unfold forcingPrice at computed
  have action:=(div_eq_iff nonzero).mp computed
  change 2*(_-_-_) = nativeStock _ h*coupling _ at action
  linear_combination -(1/2:ℂ)*action

theorem actual_stock_euler_balance (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    remainingAReturnRead (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h-
      completeBetaPrice (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h+
      forcingInventory (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h=
      sourceAction (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h (upperRadius h)-
      sourceAction (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h (lowerRadius h)-
      (coupling (OriginalJointFluxSource.Prior.coordinate observation nontrivial half)/2)*
        nativeStock (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h := by
  have source:=full_forcing_euler_reaction
    (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h nonnegative
  rw [actual_stock_generated_forcing observation nontrivial half h nonnegative bounded] at source
  exact source.symm

end OriginalCommonInverseForcing.SourceJoint.FullStock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
