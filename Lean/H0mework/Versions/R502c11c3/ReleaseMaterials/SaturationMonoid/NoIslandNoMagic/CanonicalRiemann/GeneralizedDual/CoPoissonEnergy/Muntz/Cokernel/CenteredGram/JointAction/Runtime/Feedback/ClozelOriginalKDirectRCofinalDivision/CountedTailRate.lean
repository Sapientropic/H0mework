import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong.TailRate
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticLimit

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKDirectRCofinalDivision

open Complex Filter BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology

local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw

/-- The literal next of the original Division supplies the reverse count and
its original Fourier forward count, with a single source-paid tail bound. -/
theorem actual_division_counted_tail
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) :
    let c := burnolDivisionZeroCompletedMellinCoordinate observation half.down
    let x := raw observation nontrivial half depth ordinal
    let y := raw observation nontrivial half depth (ordinal+1)
    ∃ limit : BurnolL2,
      (∀ N : Nat, FiniteForcing.source N (fourierL2 y) = fourierL2 (DualSource.source N y)) ∧
      Tendsto (fun N => (DualSource.source N y, FiniteForcing.source N (fourierL2 y))) atTop
        (𝓝 (limit, fourierL2 limit)) ∧
      ∀ M : Nat, 0 < M →
        max ‖limit-DualSource.source (M+1) y‖
            ‖fourierL2 limit-FiniteForcing.source (M+1) (fourierL2 y)‖ ≤
          (2*(M : ℝ)^(-(1/2 : ℝ)))*‖c.value • y+(2 : ℂ) • x‖ := by
  dsimp only
  let c := burnolDivisionZeroCompletedMellinCoordinate observation half.down
  let x := raw observation nontrivial half depth ordinal
  let y := raw observation nontrivial half depth (ordinal+1)
  have action : y = burnolDirectRightResolventCLM c x := by
    dsimp only [y, x, c]
    rw [OriginalKCombFirstFullSourceDynamics.raw_successor,
      OriginalKCombCofinalRAction.original_R_direct]
    rfl
  obtain ⟨limit, converges, bound⟩ := CountedJointStrong.actual_resolvent_reverse_tail c x
  change ∃ limit : BurnolL2, _ ∧
    Tendsto (fun N => (DualSource.source N y, FiniteForcing.source N (fourierL2 y))) atTop
      (𝓝 (limit, fourierL2 limit)) ∧ ∀ M : Nat, 0 < M → _
  rw [← action] at converges bound
  have same (N : Nat) : FiniteForcing.source N (fourierL2 y) = fourierL2 (DualSource.source N y) :=
    OriginalGamma.Source.CountingQuadraticLimit.source_fourier N y
  refine ⟨limit, same, ?_, ?_⟩
  · apply (converges.prodMk_nhds ((fourierL2.continuous.tendsto limit).comp converges)).congr'
    filter_upwards with N
    change (DualSource.source N y, fourierL2 (DualSource.source N y)) =
      (DualSource.source N y, FiniteForcing.source N (fourierL2 y))
    rw [same N]
  · intro M positive
    rw [same (M+1), ← map_sub, LinearIsometryEquiv.norm_map, max_self]
    exact bound M positive

end OriginalKDirectRCofinalDivision
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
