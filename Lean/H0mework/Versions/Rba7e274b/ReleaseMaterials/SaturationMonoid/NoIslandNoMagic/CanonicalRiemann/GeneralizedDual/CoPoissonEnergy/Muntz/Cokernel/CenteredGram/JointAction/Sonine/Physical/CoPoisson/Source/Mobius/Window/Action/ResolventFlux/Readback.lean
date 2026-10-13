import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Defect
import H0mework.Versions.V2.Arithmetic.RieszSynthesis.Defect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FiniteMobiusResolventFlux
open Complex
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def sourceDefect : BurnolL2 := -defectForcing observation nontrivial half-
  sourceA observation • Rplus (star observation.coordinate/2) (defectForcing observation nontrivial half)

-- The generated forcing, not a caller-selected defect, is passed through the actual resolvent inverse.
theorem original_defect_source_readback : D (Prior.originalK observation nontrivial half)=sourceDefect observation nontrivial half := by
  have starRight : 1/4<(star observation.coordinate/2).re := by
    rw [Complex.div_re]
    norm_num [Complex.star_def]
    linarith [half.down]
  have inverse := source_resolvent_inverse (observation.coordinate/2) (star observation.coordinate/2)
    (Paid.parameter_rightQuarter observation half) starRight (D (Prior.originalK observation nontrivial half))
  have scalar : star observation.coordinate/2-observation.coordinate/2=sourceA observation := by unfold sourceA;ring
  rw [scalar,original_defect_source_equation observation nontrivial half] at inverse
  exact inverse.symm

theorem original_physical_defect_source_readback : OriginalRieszFiniteSynthesis.sourceFourierDefect
    (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))=sourceDefect observation nontrivial half := by
  rw [← defect_source_physical]
  exact original_defect_source_readback observation nontrivial half

theorem original_defect_transpose_source (source : BurnolL2) :
    inner ℂ (OriginalRieszFiniteSynthesis.defectTranspose source)
      (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))=
    inner ℂ source (sourceDefect observation nontrivial half) := by
  rw [OriginalRieszFiniteSynthesis.defectTranspose_pairing,original_physical_defect_source_readback]

end FiniteMobiusResolventFlux
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
