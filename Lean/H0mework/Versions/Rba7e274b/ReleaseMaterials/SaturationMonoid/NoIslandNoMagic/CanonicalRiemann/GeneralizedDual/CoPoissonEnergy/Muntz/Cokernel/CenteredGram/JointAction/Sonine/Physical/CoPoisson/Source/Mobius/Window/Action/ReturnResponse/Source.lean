import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.CompletePrice
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalReturnResponseSource
open Complex MeasureTheory Set Filter
open scoped Topology InnerProductSpace
open OriginalRieszSource

def returnResponse (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterIntervalL2 :=
  (Constructor.returnEuler coordinate:BurnolQuarterIntervalL2)+
    (star coordinate.value-1/2) • (Constructor.returnState coordinate:BurnolQuarterIntervalL2)
def returnResponseRaw (coordinate : BurnolCompletedMellinCoordinate) (y : ℝ) : ℂ :=
  (y:ℂ)*burnolRieszReturnRawDerivative coordinate y+star coordinate.value*burnolRieszReturnRaw coordinate y-
    burnolRieszReturnRaw coordinate (1/4:ℝ)

def wholeReturnResponse (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolQuarterZeroExtension (returnResponse coordinate)

theorem actual_return_mean (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterMeanCoefficient (Constructor.returnEulerAmbient coordinate)=burnolRieszReturnRaw coordinate (1/4:ℝ) := by
  have endpoints := burnolRieszSingleFourierReturnRaw_endpoints coordinate
  change burnolRieszReturnRaw coordinate (-(1/4:ℝ))=burnolRieszReturnRaw coordinate (1/4:ℝ) at endpoints
  rw [Constructor.returnEulerAmbient_mean,endpoints]
  ring

theorem actual_return_response_read (coordinate : BurnolCompletedMellinCoordinate) :
    (returnResponse coordinate : ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval (1/4:ℝ))] returnResponseRaw coordinate := by
  have ordinary := burnolMeanZeroProjection_ae_raw (Constructor.returnEulerAmbient coordinate)
    (Constructor.returnEulerRaw coordinate) (Constructor.compact_read _ (Constructor.returnEulerRaw_continuous coordinate))
  change (Constructor.returnEuler coordinate:BurnolQuarterIntervalL2)=ᵐ[volume.restrict (symmetricInterval (1/4:ℝ))]
    (fun x=>Constructor.returnEulerRaw coordinate x-burnolQuarterMeanCoefficient (Constructor.returnEulerAmbient coordinate)) at ordinary
  rw [actual_return_mean] at ordinary
  filter_upwards [Lp.coeFn_add (Constructor.returnEuler coordinate:BurnolQuarterIntervalL2)
      ((star coordinate.value-1/2) • (Constructor.returnState coordinate:BurnolQuarterIntervalL2)),
    Lp.coeFn_smul (star coordinate.value-1/2) (Constructor.returnState coordinate:BurnolQuarterIntervalL2),
    Constructor.returnState_read coordinate,ordinary] with x added scalar source euler
  unfold returnResponse
  rw [added]
  change (Constructor.returnEuler coordinate:BurnolQuarterIntervalL2) x+
    ((star coordinate.value-1/2) • (Constructor.returnState coordinate:BurnolQuarterIntervalL2):BurnolQuarterIntervalL2) x=_
  rw [scalar]
  change (Constructor.returnEuler coordinate:BurnolQuarterIntervalL2) x+
    (star coordinate.value-1/2)*(Constructor.returnState coordinate:BurnolQuarterIntervalL2) x=_
  rw [source,euler]
  unfold Constructor.returnEulerRaw returnResponseRaw
  ring

theorem actual_return_response_whole (coordinate : BurnolCompletedMellinCoordinate) :
    (wholeReturnResponse coordinate : ℝ→ℂ)=ᵐ[volume]
      (symmetricInterval (1/4:ℝ)).indicator (returnResponseRaw coordinate) := by
  have source := (ae_restrict_iff' (measurableSet_symmetricInterval (1/4:ℝ))).mp (actual_return_response_read coordinate)
  filter_upwards [burnolQuarterZeroExtension_coe (returnResponse coordinate),source] with x extended actual
  unfold wholeReturnResponse
  rw [extended]
  by_cases inside : x∈symmetricInterval (1/4:ℝ)
  · simp only [indicator_of_mem inside]
    exact actual inside
  · simp only [indicator_of_notMem inside]

theorem original_return_response_occurrence (coordinate : BurnolCompletedMellinCoordinate) :
    OriginalColumnMomentSource.wholeReturnResponse coordinate=wholeReturnResponse coordinate := by
  unfold OriginalColumnMomentSource.wholeReturnResponse OriginalColumnMomentSource.wholeReturnEuler
    OriginalColumnMomentSource.wholeReturn wholeReturnResponse returnResponse Constructor.returnState
  rw [map_add,map_smul]

theorem actual_return_response_coefficients (coordinate : BurnolCompletedMellinCoordinate) :
    returnResponse coordinate=-(Kernel.A coordinate) • (Response.v:BurnolQuarterIntervalL2)+
      Kernel.beta coordinate • (Response.u:BurnolQuarterIntervalL2) := by
  have source := congrArg (fun state : BurnolQuarterMeanZeroCarrier=>(state:BurnolQuarterIntervalL2))
    (Euler.returnEuler_eq coordinate)
  change (Constructor.returnEuler coordinate:BurnolQuarterIntervalL2)=
    -(star coordinate.value-1/2) • (Constructor.returnState coordinate:BurnolQuarterIntervalL2)-
      Kernel.A coordinate • (Response.v:BurnolQuarterIntervalL2)+Kernel.beta coordinate • (Response.u:BurnolQuarterIntervalL2) at source
  unfold returnResponse
  rw [source]
  module

theorem actual_return_response_continuous (coordinate : BurnolCompletedMellinCoordinate) : Continuous (returnResponseRaw coordinate) := by
  unfold returnResponseRaw
  have raw := burnolRieszReturnRaw_continuous coordinate
  have derivative := burnolRieszReturnRawDerivative_continuous coordinate
  fun_prop

end OriginalReturnResponseSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
