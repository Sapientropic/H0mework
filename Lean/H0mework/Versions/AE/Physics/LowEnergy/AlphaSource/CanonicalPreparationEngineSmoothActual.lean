import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineSmoothProgram

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineSmooth
open PreparationActualFactor PreparationVacuumEngineSource PreparationVacuumClockSymbol
open PreparationVacuumClockJacobian PreparationVacuumWeyl
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff

theorem sourceEngine_smooth (k : ℕ) : SmoothClock (sourceEngine k) := by
  induction k with
  | zero =>
    intro a j
    have first : j=(0 : Fin 1) := by apply Fin.ext; have := j.isLt; omega
    rw [first,sourceEngine_initial]
    split_ifs
    · exact sourceClock_smooth
    · exact smoothSymbol_zero
  | succ k ih =>
    intro a j
    change SmoothSymbol (if h : j.val<k+1 then sourceEngine k a ⟨j.val,h⟩
      else (smooth_program_const% "generatedCorrection") (sourceEngine k) a)
    split_ifs
    · exact ih _ _
    · intro x hx
      change ContDiffWithinAt ℝ ∞ (fun q => -∑ b : Fin 4,
        (principalForceJacobian q)⁻¹ a b*
          forceOrEnergy (k+1) (sourceEngine k) (some b) (Fin.last (k+1)) q) poleDomain x
      apply ContDiffWithinAt.neg
      apply ContDiffWithinAt.sum
      intro b _
      exact ((source_engineInverse_smooth a b) x hx).mul
        ((forceOrEnergy_program_smooth (k+1) ih (some b) (Fin.last (k+1))) x hx)

theorem sourceEngineEnergy_smooth (k : ℕ) : SmoothSymbol (sourceEngineEnergy k) :=
  forceOrEnergy_program_smooth k (sourceEngine_smooth k) none (Fin.last k)

theorem sourceEngineForces_smooth (k : ℕ) (a : Fin 4) : SmoothSymbol (sourceEngineForces k a) :=
  forceOrEnergy_program_smooth k (sourceEngine_smooth k) (some a) (Fin.last k)

theorem actual_clock_coefficient_smooth (k : ℕ) (a : Fin 4) (j : Fin (k+1))
    (z : FlatConfiguration) (p : PhysicalMomentum)
    (position : z ∈ thetaPositionClosed) (direction : normalizedMomentum p ∈ thetaDirectionClosed)
    (nonzero : p ≠ 0) : ContDiffAt ℝ ∞ (sourceEngine k a j) (z,p) :=
  ((sourceEngine_smooth k a j) (z,p) (source_support_admitted z p position direction nonzero)).contDiffAt
    (poleDomain_open.mem_nhds (source_support_admitted z p position direction nonzero))

theorem actual_energy_coefficient_smooth (k : ℕ) (z : FlatConfiguration) (p : PhysicalMomentum)
    (position : z ∈ thetaPositionClosed) (direction : normalizedMomentum p ∈ thetaDirectionClosed)
    (nonzero : p ≠ 0) : ContDiffAt ℝ ∞ (sourceEngineEnergy k) (z,p) :=
  ((sourceEngineEnergy_smooth k) (z,p) (source_support_admitted z p position direction nonzero)).contDiffAt
    (poleDomain_open.mem_nhds (source_support_admitted z p position direction nonzero))

theorem actual_force_coefficient_smooth (k : ℕ) (a : Fin 4) (z : FlatConfiguration) (p : PhysicalMomentum)
    (position : z ∈ thetaPositionClosed) (direction : normalizedMomentum p ∈ thetaDirectionClosed)
    (nonzero : p ≠ 0) : ContDiffAt ℝ ∞ (sourceEngineForces k a) (z,p) :=
  ((sourceEngineForces_smooth k a) (z,p) (source_support_admitted z p position direction nonzero)).contDiffAt
    (poleDomain_open.mem_nhds (source_support_admitted z p position direction nonzero))

theorem actual_energy_word_smooth (k r : ℕ) (w : PreparationVacuumCanonicalMoyal.Word r)
    (z : FlatConfiguration) (p : PhysicalMomentum)
    (position : z ∈ thetaPositionClosed) (direction : normalizedMomentum p ∈ thetaDirectionClosed)
    (nonzero : p ≠ 0) : ContDiffAt ℝ ∞
      (fun q => PreparationVacuumCanonicalMoyal.jet r (sourceEngineEnergy k) w q) (z,p) := by
  have admitted := source_support_admitted z p position direction nonzero
  exact ((smoothSymbol_jet r w (sourceEngineEnergy_smooth k)) (z,p) admitted).contDiffAt
    (poleDomain_open.mem_nhds admitted)

end LowEnergy.PreparationVacuumEngineSmooth
