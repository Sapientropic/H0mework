import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalContactFeedbackSource
open Complex MeasureTheory FourierTransform
open scoped InnerProductSpace FourierTransform
open OriginalRieszSource
namespace C
export OriginalColumnMomentSource (originalB wholeContactResponse wholeReturn wholeReturnEuler contactResponse)
end C

def sourceField (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2 (C.originalB coordinate)+Kernel.beta coordinate • OriginalRieszFiniteSource.fourierPrimitive coordinate

def sourceForcing (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2 (C.wholeContactResponse coordinate)-
    (2*(star coordinate.value-1/2)*Kernel.beta coordinate) • OriginalRieszFiniteSource.fourierPrimitive coordinate

def sourceVelocity (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  -(star coordinate.value-1/2) • sourceField coordinate-sourceForcing coordinate

-- The two original source laws cancel their own Edge forcing before the finite operator acts.
theorem combined_source_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (sourceField coordinate:TemperedDistribution ℝ ℂ)=
      (sourceVelocity coordinate:TemperedDistribution ℝ ℂ) := by
  have source := congrArg (fourierCLM ℂ (TemperedDistribution ℝ ℂ)) (Euler.source_euler coordinate)
  have solved := Euler.sourceEuler_eq coordinate
  have sourceSplit : OriginalColumnMomentSource.wholeSourceEuler coordinate=
      (star coordinate.value-1/2) • C.originalB coordinate+C.wholeContactResponse coordinate := by
    have actual := congrArg (fun v : BurnolQuarterMeanZeroCarrier=>burnolQuarterZeroExtension (v:BurnolQuarterIntervalL2)) solved
    change OriginalColumnMomentSource.wholeSourceEuler coordinate=burnolQuarterZeroExtension
      ((star coordinate.value-1/2) • (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2)+
        Kernel.A coordinate • (Response.u:BurnolQuarterIntervalL2)-Kernel.beta coordinate • (Response.v:BurnolQuarterIntervalL2)) at actual
    rw [actual]
    unfold C.originalB C.wholeContactResponse C.contactResponse
    simp only [map_sub,map_add,map_smul]
    module
  change 𝓕 (GapEuler.euler (C.originalB coordinate:TemperedDistribution ℝ ℂ))=
    𝓕 (OriginalColumnMomentSource.wholeSourceEuler coordinate:TemperedDistribution ℝ ℂ)-
      Kernel.beta coordinate • 𝓕 (GapEuler.edge (1/4:ℝ)) at source
  have anti : 𝓕 (GapEuler.euler (C.originalB coordinate:TemperedDistribution ℝ ℂ))=
      -GapEuler.euler (𝓕 (C.originalB coordinate:TemperedDistribution ℝ ℂ)) := by
    rw [GapEuler.euler_fourier,neg_neg]
  rw [anti] at source
  have wholeF (value : BurnolL2) : 𝓕 (value:TemperedDistribution ℝ ℂ)=(fourierL2 value:TemperedDistribution ℝ ℂ) :=
    Lp.fourier_toTemperedDistribution_eq value
  rw [wholeF,sourceSplit,wholeF] at source
  have primitive := OriginalRieszFiniteSource.fourierPrimitive_euler coordinate
  unfold sourceVelocity sourceField sourceForcing
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (_+_))=
    Lp.toTemperedDistributionCLM ℂ volume 2 (_-_)
  simp only [map_add,map_smul,map_sub,Lp.toTemperedDistributionCLM_apply]
  have first : GapEuler.euler (fourierL2 (C.originalB coordinate):TemperedDistribution ℝ ℂ)=
      -(star coordinate.value-1/2) • (fourierL2 (C.originalB coordinate):TemperedDistribution ℝ ℂ)-
        (fourierL2 (C.wholeContactResponse coordinate):TemperedDistribution ℝ ℂ)+
          Kernel.beta coordinate • 𝓕 (GapEuler.edge (1/4:ℝ)) := by
    change -GapEuler.euler (fourierL2 (C.originalB coordinate):TemperedDistribution ℝ ℂ)=
      Lp.toTemperedDistributionCLM ℂ volume 2 (fourierL2 ((star coordinate.value-1/2) • C.originalB coordinate+C.wholeContactResponse coordinate))-Kernel.beta coordinate • 𝓕 (GapEuler.edge (1/4:ℝ)) at source
    simp only [map_add,map_smul,Lp.toTemperedDistributionCLM_apply] at source
    have negated := congrArg (fun v : TemperedDistribution ℝ ℂ=>-v) source
    rw [neg_neg] at negated
    rw [negated]
    module
  rw [first,eq_sub_of_add_eq primitive]
  module

 theorem combined_source_strong (coordinate : BurnolCompletedMellinCoordinate) :
    HasDerivAt (fun h : ℝ=>burnolMultiplicativeDilation h (sourceField coordinate))
      (sourceVelocity coordinate) 0 :=
  OriginalRieszFinitePairing.CoPoisson.Ward.DilationWard.strong_derivative _ _ (combined_source_euler coordinate)

end OriginalContactFeedbackSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
