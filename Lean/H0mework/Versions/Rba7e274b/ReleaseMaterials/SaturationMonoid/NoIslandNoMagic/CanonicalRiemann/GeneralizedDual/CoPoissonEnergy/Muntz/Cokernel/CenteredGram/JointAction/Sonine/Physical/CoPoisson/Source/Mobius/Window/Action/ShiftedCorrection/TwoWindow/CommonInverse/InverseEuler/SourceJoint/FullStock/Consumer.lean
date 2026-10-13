import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.FullStock.Boundary

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.SourceJoint.FullStock
open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszFiniteSource OriginalRieszFiniteSynthesis OriginalCommonInverseForcing.InverseEuler
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

theorem original_complete_native_stock_price (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    OriginalRieszFiniteColumns.firstSourceRead (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h
        (burnolCompletedMellinRieszVector (OriginalJointFluxSource.Prior.coordinate observation nontrivial half))+
      OriginalRieszFiniteColumns.firstSourceRead (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) (-h)
        (burnolCompletedMellinRieszVector (OriginalJointFluxSource.Prior.coordinate observation nontrivial half))+
      OriginalInverseReturnActionSource.completeInverseReturnPrice observation nontrivial half h=
      -nativeStock (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h := by
  rw [← actual_stock_complete_forcing observation nontrivial half h nonnegative bounded]
  exact OriginalTwoWindowInverseForcing.original_complete_forcing_action_price observation nontrivial half h nonnegative bounded

theorem original_fixed_residual_native_stock :
    -burnolPaFixedShiftResidual (OriginalJointFluxSource.Prior.coordinate observation nontrivial half)
      (by rw [OriginalJointFluxSource.Prior.coordinate_value];exact observation.mathlibZero)=
      (pairedMellinTranslationCharacter observation.coordinate (Real.log stageZeroSonineQ)-
        pairedMellinTranslationCharacter (star observation.coordinate) (Real.log stageZeroSonineQ))*
          OriginalRieszFinitePairing.kernelSelfSource (OriginalJointFluxSource.Prior.coordinate observation nontrivial half)+
        (1/2:ℂ)*star (nativeStock (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) (Real.log stageZeroSonineQ)) := by
  rw [← actual_stock_complete_forcing observation nontrivial half (Real.log stageZeroSonineQ)
    (by apply Real.log_nonneg;change 1≤Real.sqrt 3;exact Real.one_le_sqrt.mpr (by norm_num))
    ((le_abs_self _).trans OriginalRieszFiniteColumns.fixedShift_small)]
  exact OriginalTwoWindowInverseForcing.original_fixed_residual_forcing_action_price observation nontrivial half

/-- The independent consumer reads both actual source equations and the literal
orthogonal boundary. It does not receive an A-return, a boundary or a price. -/
theorem consume_full_source_action (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    (type_of% (actual_whole_synthesis_source (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) h nonnegative bounded)) ∧
    (type_of% (actual_whole_boundary_source (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) observation.mathlibZero h nonnegative bounded)) ∧
    (type_of% (actual_orthogonal_boundary_source (OriginalJointFluxSource.Prior.coordinate observation nontrivial half) observation.mathlibZero h nonnegative bounded)) ∧
    (type_of% (actual_stock_euler_balance observation nontrivial half h nonnegative bounded)) ∧
    (type_of% (original_complete_native_stock_price observation nontrivial half h nonnegative bounded)) :=
  ⟨actual_whole_synthesis_source _ h nonnegative bounded,
    actual_whole_boundary_source _ observation.mathlibZero h nonnegative bounded,
    actual_orthogonal_boundary_source _ observation.mathlibZero h nonnegative bounded,
    actual_stock_euler_balance observation nontrivial half h nonnegative bounded,
    original_complete_native_stock_price observation nontrivial half h nonnegative bounded⟩

end OriginalCommonInverseForcing.SourceJoint.FullStock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
