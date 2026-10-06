import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationWholeBudget

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTailSupport
open PreparationVacuumWholeTail PreparationVacuumLocalizedTail PreparationVacuumOriginalRadii
open PreparationVacuumCanonicalMoyal PreparationVacuumConicComposition PreparationVacuumConicBudget
open PreparationVacuumClockSymbol PreparationVacuumWeyl PreparationVacuumEnergyTail
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol
abbrev ArrayBound := ℕ → ℝ

theorem energyTailFor_theta_zero (B : ℕ → Fin 5 → ArrayBound) (x : Phase)
    (zero : sourceConicTheta x=0) : energyTailFor B x=0 := by
  have vanish : ∀ j : ℕ,energyTailTerm B (j+2) x=0 := by
    intro j
    simp only [energyTailTerm,localizedEnergy,zero,zero_mul]
  unfold energyTailFor
  simp_rw [vanish]
  simp

theorem energyTailFor_position_zero (B : ℕ → Fin 5 → ArrayBound) (x : Phase)
    (outside : x.1∉thetaPositionClosed) : energyTailFor B x=0 := by
  apply energyTailFor_theta_zero B x
  rw [sourceConicTheta_native]
  exact sourceTheta_zero_position outside

theorem energyTailFor_position_germ (B : ℕ → Fin 5 → ArrayBound) (x : Phase)
    (outside : x.1∉thetaPositionClosed) : energyTailFor B=ᶠ[𝓝 x] (fun _=>0) := by
  have near : ∀ᶠ y : Phase in 𝓝 x,y.1∉thetaPositionClosed :=
    (thetaPositionClosed_closed.isOpen_compl.preimage continuous_fst).mem_nhds outside
  filter_upwards [near] with y hy
  exact energyTailFor_position_zero B y hy

theorem normalizedCoordinate_smooth (i : Fin 100) (x : Phase) (nonzero : x.2≠0) :
    ContDiffAt ℝ ∞ (fun y : Phase=>normalizedMomentum y.2 i) x := by
  have coordinate : ContDiff ℝ ∞ (fun y : Phase=>y.2 i) :=
    PreparationVacuumPrincipalBudget.momentumCoordinate i |>.contDiff
  have normSmooth : ContDiffAt ℝ ∞ (fun y : Phase=>‖y.2‖) x :=
    (contDiffAt_norm ℝ nonzero).comp x contDiffAt_snd
  exact coordinate.contDiffAt.div normSmooth (norm_ne_zero_iff.mpr nonzero)

theorem energyTailFor_direction_germ (B : ℕ → Fin 5 → ArrayBound) (x : Phase)
    (nonzero : x.2≠0) (outside : normalizedMomentum x.2∉thetaDirectionClosed) :
    energyTailFor B=ᶠ[𝓝 x] (fun _=>0) := by
  have failed : ¬∀ i,|normalizedMomentum x.2 i-sourceUnitMomentum i|≤ sourceRadius:=outside
  push Not at failed
  obtain ⟨i,hi⟩:=failed
  have continuous : ContinuousAt (fun y : Phase=>|normalizedMomentum y.2 i-sourceUnitMomentum i|) x :=
    ((normalizedCoordinate_smooth i x nonzero).continuousAt.sub continuousAt_const).abs
  have near : ∀ᶠ y : Phase in 𝓝 x,sourceRadius< |normalizedMomentum y.2 i-sourceUnitMomentum i| :=
    continuous.eventually (lt_mem_nhds hi)
  filter_upwards [near] with y hy
  apply energyTailFor_theta_zero B y
  rw [sourceConicTheta_native]
  apply sourceTheta_zero_direction
  intro closed
  exact (not_lt_of_ge (closed i)) hy

theorem energyTailFor_global_smooth (B : ℕ → Fin 5 → ArrayBound) :
    ContDiff ℝ ∞ (energyTailFor B) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases nonzero : x.2=0
  · exact contDiffAt_const.congr_of_eventuallyEq
      (energyTailFor_low_germ B x (by simp [nonzero]))
  · by_cases position : x.1∈thetaPositionClosed
    · by_cases direction : normalizedMomentum x.2∈thetaDirectionClosed
      · exact energyTailFor_smooth B x (source_support_admitted x.1 x.2 position direction nonzero)
      · exact contDiffAt_const.congr_of_eventuallyEq (energyTailFor_direction_germ B x nonzero direction)
    · exact contDiffAt_const.congr_of_eventuallyEq (energyTailFor_position_germ B x position)

end LowEnergy.PreparationVacuumTailSupport
