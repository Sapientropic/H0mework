import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Readback
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.ZeroRead
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FiniteMobiusResolventFlux
open Complex MeasureTheory
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open OriginalRieszFiniteColumns OriginalRieszFiniteSynthesis
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

theorem original_whole_read_source (shift : ℝ) :
    wholeSourceRead (Prior.coordinate observation nontrivial half) shift
      (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half)) =
    firstSourceRead (Prior.coordinate observation nontrivial half) shift
      (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
    inner ℂ (burnolAnnulusSamplingL2 (fourierColumn (Prior.coordinate observation nontrivial half) shift) 0)
      (sourceDefect observation nontrivial half) := by
  rw [wholeSourceRead_keeps_defect,original_physical_defect_source_readback]

theorem original_correction_source (shift : ℝ) (nonnegative : 0≤shift) (bounded : shift≤Real.log 2) :
    OriginalRieszFinitePairing.CoPoisson.correctionRead (Prior.coordinate observation nontrivial half) shift =
      -(firstSourceRead (Prior.coordinate observation nontrivial half) shift
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        firstSourceRead (Prior.coordinate observation nontrivial half) (-shift)
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
        inner ℂ (burnolAnnulusSamplingL2 (fourierColumn (Prior.coordinate observation nontrivial half) shift) 0+
          burnolAnnulusSamplingL2 (fourierColumn (Prior.coordinate observation nontrivial half) (-shift)) 0)
          (sourceDefect observation nontrivial half)) := by
  have zero : riemannZeta (Prior.coordinate observation nontrivial half).value=0 := by
    rw [Prior.coordinate_value]
    exact observation.mathlibZero
  have actual := OriginalRieszFinitePairing.CoPoisson.original_tate_correction
    (Prior.coordinate observation nontrivial half) zero shift nonnegative bounded
  rw [original_physical_defect_source_readback observation nontrivial half] at actual
  exact (neg_eq_iff_eq_neg.mpr actual).symm

end FiniteMobiusResolventFlux
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
