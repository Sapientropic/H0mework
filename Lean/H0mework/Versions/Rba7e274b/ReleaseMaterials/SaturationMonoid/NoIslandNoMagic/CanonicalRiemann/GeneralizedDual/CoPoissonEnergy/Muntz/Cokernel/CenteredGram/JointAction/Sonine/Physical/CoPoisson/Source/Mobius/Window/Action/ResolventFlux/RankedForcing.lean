import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.ReverseRank
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Correction
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

-- Both finite means and the signed exterior source are generated from the actual K occurrence.
def rankedDefectFlux (coordinate : BurnolCompletedMellinCoordinate) (value : Ambient) : BurnolL2 :=
  reverseRankSource coordinate (fourierL2 (value : BurnolL2))+
  (2*innerTailMoment coordinate value) • burnolTateReciprocalL2 (exteriorBase coordinate)

theorem defect_flux_ranked (coordinate : BurnolCompletedMellinCoordinate) (value : Ambient) :
    defectFlux (coordinate.value/2) (value : BurnolL2)=rankedDefectFlux coordinate value := by
  unfold defectFlux rankedDefectFlux
  have fourierPhysical : (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value : BurnolL2)=fourierL2 (value : BurnolL2) := rfl
  rw [← fourierPhysical,source_reverse_flux_three_base,source_forward_flux_rank_one,map_smul,neg_smul,sub_neg_eq_add]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def rankedForcing : BurnolL2 := D (primitiveSource observation nontrivial half)-sourceA observation •
  rankedDefectFlux (Prior.coordinate observation nontrivial half)
    (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))

def rankedSourceDefect : BurnolL2 := -rankedForcing observation nontrivial half-
  sourceA observation • Rplus (star observation.coordinate/2) (rankedForcing observation nontrivial half)

theorem original_forcing_ranked : defectForcing observation nontrivial half=rankedForcing observation nontrivial half := by
  unfold defectForcing rankedForcing
  have same : (Prior.coordinate observation nontrivial half).value=observation.coordinate := Prior.coordinate_value observation nontrivial half
  have rank := defect_flux_ranked (Prior.coordinate observation nontrivial half)
    (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))
  rw [same] at rank
  change D (primitiveSource observation nontrivial half)-sourceA observation • defectFlux (observation.coordinate/2)
    (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half) : BurnolL2)=_
  rw [rank]

theorem original_defect_ranked : OriginalRieszFiniteSynthesis.sourceFourierDefect
    (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))=rankedSourceDefect observation nontrivial half := by
  rw [original_physical_defect_source_readback]
  unfold sourceDefect rankedSourceDefect
  rw [original_forcing_ranked]

theorem original_transpose_ranked (source : BurnolL2) :
    inner ℂ (OriginalRieszFiniteSynthesis.defectTranspose source)
      (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))=
    inner ℂ source (rankedSourceDefect observation nontrivial half) := by
  rw [OriginalRieszFiniteSynthesis.defectTranspose_pairing,original_defect_ranked]

theorem original_whole_ranked (shift : ℝ) :
    OriginalRieszFiniteSynthesis.wholeSourceRead (Prior.coordinate observation nontrivial half) shift
      (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))=
      OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) shift
      (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
      inner ℂ (burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn (Prior.coordinate observation nontrivial half) shift) 0)
        (rankedSourceDefect observation nontrivial half) := by
  rw [OriginalRieszFiniteSynthesis.wholeSourceRead_keeps_defect,original_defect_ranked]

theorem original_correction_ranked (shift : ℝ) (nonnegative : 0≤shift) (bounded : shift≤Real.log 2) :
    OriginalRieszFinitePairing.CoPoisson.correctionRead (Prior.coordinate observation nontrivial half) shift=
    -(OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) shift
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
      OriginalRieszFiniteColumns.firstSourceRead (Prior.coordinate observation nontrivial half) (-shift)
          (burnolCompletedMellinRieszVector (Prior.coordinate observation nontrivial half))+
      inner ℂ (burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn (Prior.coordinate observation nontrivial half) shift) 0+
          burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn (Prior.coordinate observation nontrivial half) (-shift)) 0)
          (rankedSourceDefect observation nontrivial half)) := by
  have source := original_correction_source observation nontrivial half shift nonnegative bounded
  unfold sourceDefect at source
  rw [original_forcing_ranked] at source
  exact source

-- An actual additive update retains its own full defect; no even/Pa qualification is transferred.
theorem actual_defect_update (increment : BurnolL2) :
    D (Prior.originalK observation nontrivial half+increment)=rankedSourceDefect observation nontrivial half+D increment := by
  rw [map_add]
  have original := original_defect_ranked observation nontrivial half
  rw [← defect_source_physical] at original
  change D (Prior.originalK observation nontrivial half)=_ at original
  rw [original]

end FiniteMobiusResolventFlux
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
