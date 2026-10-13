import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ReturnResponse.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalReturnResponseSource
open Complex MeasureTheory
open scoped InnerProductSpace Topology
open OriginalRieszSource
attribute [local instance 1100] NormedSpace.complexToReal

def correctedReturn (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  OriginalColumnMomentSource.wholeReturn coordinate+
    burnolRieszReturnRaw coordinate (1/4:ℝ) • OriginalRieszFiniteSource.edgePrimitive coordinate

def correctedVelocity (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  -(star coordinate.value-1/2) • correctedReturn coordinate+wholeReturnResponse coordinate

-- The original return endpoint is paid by the same actual gap/tail primitive.
theorem original_return_euler_source (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (correctedReturn coordinate:TemperedDistribution ℝ ℂ)=
      (correctedVelocity coordinate:TemperedDistribution ℝ ℂ) := by
  have returned := Euler.return_euler coordinate
  have primitive := OriginalRieszFiniteSource.edgePrimitive_euler coordinate
  have primitiveLaw := eq_sub_of_add_eq primitive
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (correctedReturn coordinate))=
    Lp.toTemperedDistributionCLM ℂ volume 2 (correctedVelocity coordinate)
  unfold correctedVelocity correctedReturn wholeReturnResponse returnResponse
  simp only [map_add,map_smul,Lp.toTemperedDistributionCLM_apply]
  change GapEuler.euler (burnolQuarterZeroExtension (Constructor.returnState coordinate:BurnolQuarterIntervalL2):TemperedDistribution ℝ ℂ)+
    burnolRieszReturnRaw coordinate (1/4:ℝ) • GapEuler.euler (OriginalRieszFiniteSource.edgePrimitive coordinate:TemperedDistribution ℝ ℂ)=_
  rw [returned,primitiveLaw]
  simp only [OriginalColumnMomentSource.wholeReturn,Constructor.returnState]
  module

 theorem original_return_ordinary_strong (coordinate : BurnolCompletedMellinCoordinate) :
    HasDerivAt (fun shift : ℝ=>burnolMultiplicativeDilation shift (correctedReturn coordinate))
      (correctedVelocity coordinate) 0 :=
  OriginalRieszFinitePairing.CoPoisson.Ward.DilationWard.strong_derivative _ _ (original_return_euler_source coordinate)

-- The actual strong source equation fixes the return and its factor; no return equality is an input.
theorem original_R_return_response (coordinate : BurnolCompletedMellinCoordinate) :
    burnolDirectRightResolvent (star coordinate.value/2) (wholeReturnResponse coordinate)=
      -(2:ℂ) • correctedReturn coordinate := by
  have right : 1/4<(star coordinate.value/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  have scalar : HasDerivAt (fun time : ℝ=>-time/2) (-1/2:ℝ) 0 := by
    simpa only [id_eq,Pi.neg_apply] using (hasDerivAt_id (0:ℝ)).neg.div_const (2:ℝ)
  have ordinary := (original_return_ordinary_strong coordinate).const_smul (-(2:ℂ))
  have actual := HasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) ordinary.hasFDerivAt scalar (by norm_num)
  have source : HasDerivAt (fun time : ℝ=>burnolMultiplicativeDilation (-time/2) (-(2:ℂ) • correctedReturn coordinate))
      ((star coordinate.value/2-1/4) • (-(2:ℂ) • correctedReturn coordinate)+wholeReturnResponse coordinate) 0 := by
    convert! actual using 1
    · funext time
      rw [map_smul]
      rfl
    · change _=(-1/2:ℝ) • (-(2:ℂ) • correctedVelocity coordinate)
      rw [← algebraMap_smul ℂ (-1/2:ℝ)]
      unfold correctedVelocity
      norm_num only [map_div₀,map_neg,map_one,map_ofNat]
      module
  exact (burnolDirectRightResolvent_of_strongEquation (star coordinate.value/2) right
    (wholeReturnResponse coordinate) (-(2:ℂ) • correctedReturn coordinate) source).symm

end OriginalReturnResponseSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
