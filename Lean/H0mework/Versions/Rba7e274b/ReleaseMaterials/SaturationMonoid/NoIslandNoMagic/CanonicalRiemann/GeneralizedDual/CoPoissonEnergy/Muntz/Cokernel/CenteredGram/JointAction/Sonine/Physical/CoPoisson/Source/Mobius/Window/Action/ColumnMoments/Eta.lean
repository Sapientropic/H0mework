import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.Contact
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszSource

def wholeSourceEuler (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolQuarterZeroExtension (Euler.sourceEuler coordinate:BurnolQuarterIntervalL2)
def wholeReturnEuler (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolQuarterZeroExtension (Constructor.returnEuler coordinate:BurnolQuarterIntervalL2)
def wholeReturn (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolQuarterZeroExtension
    (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate):BurnolQuarterIntervalL2)

def generatedEta (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2 (wholeSourceEuler coordinate-(star coordinate.value-1/2) • originalB coordinate)+
    (wholeReturnEuler coordinate+(star coordinate.value-1/2) • wholeReturn coordinate)-
      (2*(star coordinate.value-1/2)*Kernel.beta coordinate) • OriginalRieszFiniteSource.fourierPrimitive coordinate

-- The same b/Sb Ward source pays the complete regular source, including the Fourier endpoint price.
theorem original_eta_source (coordinate : BurnolCompletedMellinCoordinate) :
    FiniteMobiusResolventFlux.S.regularSource coordinate=generatedEta coordinate := by
  have source := congrArg (fun v : BurnolQuarterMeanZeroCarrier=>burnolQuarterZeroExtension (v:BurnolQuarterIntervalL2))
    (Euler.sourceEuler_eq coordinate)
  have returned := congrArg (fun v : BurnolQuarterMeanZeroCarrier=>burnolQuarterZeroExtension (v:BurnolQuarterIntervalL2))
    (Euler.returnEuler_eq coordinate)
  change wholeSourceEuler coordinate=burnolQuarterZeroExtension
    ((star coordinate.value-1/2) • (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2)+
      Kernel.A coordinate • (Response.u:BurnolQuarterIntervalL2)-Kernel.beta coordinate • (Response.v:BurnolQuarterIntervalL2)) at source
  change wholeReturnEuler coordinate=burnolQuarterZeroExtension
    ((-(star coordinate.value-1/2)) •
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate):BurnolQuarterIntervalL2)-
      Kernel.A coordinate • (Response.v:BurnolQuarterIntervalL2)+Kernel.beta coordinate • (Response.u:BurnolQuarterIntervalL2)) at returned
  simp only [map_sub,map_add,map_smul] at source returned
  unfold generatedEta
  rw [source,returned]
  unfold originalB wholeReturn FiniteMobiusResolventFlux.S.regularSource Response.wholeU Response.wholeV
  simp only [map_sub,map_add,map_smul]
  module

 theorem original_eta_defect_source (coordinate : BurnolCompletedMellinCoordinate) :
    S.D (FiniteMobiusResolventFlux.S.regularSource coordinate)=S.D (generatedEta coordinate) := by
  rw [original_eta_source]

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
