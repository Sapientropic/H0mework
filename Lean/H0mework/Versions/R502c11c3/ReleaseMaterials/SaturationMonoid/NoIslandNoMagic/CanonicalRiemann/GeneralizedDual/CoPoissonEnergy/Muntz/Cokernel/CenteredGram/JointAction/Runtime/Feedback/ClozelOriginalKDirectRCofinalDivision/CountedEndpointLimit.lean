import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.EndpointLimit
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CompactWave
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedTailRate

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKDirectRCofinalDivision

open Complex Filter BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward CountedJointStrong
open scoped Topology


private theorem endpoint_scale_fourier (d : ℝ) (N : Nat) (value : BurnolL2) :
    fourierL2 (countEndpointScale d N value) = countEndpointScale (-d) N (fourierL2 value) := by
  change fourierL2 ((Real.sqrt (N : ℝ) : ℂ) •
    burnolMultiplicativeDilation (-(d*Real.log (N : ℝ))) value) =
    (Real.sqrt (N : ℝ) : ℂ) • burnolMultiplicativeDilation (-(-d*Real.log (N : ℝ))) (fourierL2 value)
  rw [map_smul, fourierL2_burnolMultiplicativeDilation, neg_mul]

/-- Both original counts use the same cutoff, and their scaled tails recover
half the literal next field and half its computed Hilbert wave. -/
theorem actual_division_counted_endpoint_limit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) :
    let wave := actualDivisionCompactWave observation nontrivial half depth ordinal
    let y := fourierL2.symm wave
    ∃ limit : BurnolL2,
      (∀ N : Nat, FiniteForcing.source N wave = fourierL2 (DualSource.source N y)) ∧
      Tendsto (fun N => (DualSource.source N y, FiniteForcing.source N wave)) atTop
        (𝓝 (limit, fourierL2 limit)) ∧
      Tendsto (fun M : Nat => (countEndpointScale 1 (M+1) (limit-DualSource.source (M+1) y),
        countEndpointScale (-1) (M+1) (fourierL2 limit-FiniteForcing.source (M+1) wave)))
        atTop (𝓝 ((1/2 : ℝ) • y, (1/2 : ℝ) • wave)) := by
  dsimp only
  let c := burnolDivisionZeroCompletedMellinCoordinate observation half.down
  let x := D.raw observation nontrivial half depth ordinal
  let native := D.raw observation nontrivial half depth (ordinal+1)
  let wave := actualDivisionCompactWave observation nontrivial half depth ordinal
  let y := fourierL2.symm wave
  have waveRead : fourierL2 y = wave := fourierL2.apply_symm_apply _
  have born := (actual_division_compact_wave_writeback observation nontrivial half depth ordinal).2.1
  have actualBorn : DirectRDivisionControls.bornRead observation nontrivial half depth ordinal =
      P.R observation nontrivial half x :=
    (Parent.Full.complete_of_branches observation nontrivial half _ _
      (OriginalKDirectRCofinalMaterial.actual_successor_branches observation nontrivial half depth ordinal)).2.2.1
  have next : native = P.R observation nontrivial half x :=
    OriginalKCombFirstFullSourceDynamics.raw_successor observation nontrivial half depth ordinal
  have returns : y = native := born.trans (actualBorn.trans next.symm)
  have action : y = burnolDirectRightResolventCLM c x := by
    rw [returns, next, OriginalKCombCofinalRAction.original_R_direct]
    rfl
  obtain ⟨limit, commutes, counted, _⟩ := actual_division_counted_tail observation nontrivial half depth ordinal
  change (∀ N : Nat, FiniteForcing.source N (fourierL2 native) = fourierL2 (DualSource.source N native)) at commutes
  change Tendsto (fun N => (DualSource.source N native, FiniteForcing.source N (fourierL2 native)))
    atTop (𝓝 (limit, fourierL2 limit)) at counted
  rw [← returns, waveRead] at commutes counted
  have moved : Tendsto (fun M : Nat => countEndpointScale 1 (M+1) (limit-DualSource.source (M+1) y))
      atTop (𝓝 ((1/2 : ℝ) • y)) := by
    rw [action]
    exact actual_resolvent_counted_endpoint_limit c x limit (by
      have source := counted.fst_nhds
      change Tendsto (fun N => DualSource.source N y) atTop (𝓝 limit) at source
      rwa [action] at source)
  have halfWave : fourierL2 ((1/2 : ℝ) • y) = (1/2 : ℝ) • wave := by
    have maps := (fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).map_smul (1/2 : ℝ) y
    change fourierL2 ((1/2 : ℝ) • y) = (1/2 : ℝ) • fourierL2 y at maps
    rwa [waveRead] at maps
  have waveMoved := (fourierL2.continuous.tendsto _).comp moved
  rw [halfWave] at waveMoved
  refine ⟨limit, commutes, counted, moved.prodMk_nhds ?_⟩
  apply waveMoved.congr'
  filter_upwards with M
  change fourierL2 (countEndpointScale 1 (M+1) (limit-DualSource.source (M+1) y)) = _
  rw [endpoint_scale_fourier, map_sub, ← commutes]

end OriginalKDirectRCofinalDivision
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
