import H0mework.Physics.GlobalOrbit.Uniform
import H0mework.Physics.NonlinearOrbit.Acceptance

/-! A smooth compact extension of the original mechanical field. The
source energy bounds will prove this cutoff equals one on its entire orbit. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
open Stage9C.Material.SpinPair Set Metric

noncomputable section

abbrev Mechanical := ℝ × ℝ

def mechanicalField (state : Mechanical) : Mechanical :=
  ((generator (state.1, state.2, 0)).1, (generator (state.1, state.2, 0)).2.1)

theorem mechanicalField_eq (state : Mechanical) :
    mechanicalField state = (state.2/inertia, -restoring state.1) := by
  rw [mechanicalField, generator_eq]

theorem mechanicalField_contDiff : ContDiff ℝ 1 mechanicalField := by
  have embedding : ContDiff ℝ 1 (fun state : Mechanical => (state.1, state.2, (0 : ℝ))) :=
    contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
  exact (generator_contDiff.comp embedding).fst.prodMk (generator_contDiff.comp embedding).snd.fst

def center : Mechanical := (gaugeScale, 0)
def initialMechanical (impulse : ℝ) : Mechanical := (gaugeScale, impulse)
def excess (impulse : ℝ) : ℝ := impulse^2/(2*inertia)
def coercivity : ℝ := 3*gaugeScale^2/(2*sourceCoupling*lapse)

theorem coercivity_pos : 0 < coercivity := by
  unfold coercivity
  rw [sourceCoupling_eq]
  exact div_pos (mul_pos (by norm_num) (pow_pos gaugeScale_pos 2)) (mul_pos (by norm_num) lapse_pos)

theorem excess_nonnegative (impulse : ℝ) : 0 ≤ excess impulse :=
  div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (by norm_num) inertia_pos))

def radius (impulse : ℝ) : ℝ := 2+impulse^2+excess impulse/coercivity

theorem radius_pos (impulse : ℝ) : 0 < radius impulse := by
  have nonnegative := div_nonneg (excess_nonnegative impulse) (le_of_lt coercivity_pos)
  unfold radius
  positivity

def cutoff (impulse : ℝ) : ContDiffBump center where
  rIn := radius impulse
  rOut := radius impulse+1
  rIn_pos := radius_pos impulse
  rIn_lt_rOut := by linarith

def compactField (impulse : ℝ) (state : Mechanical) : Mechanical := cutoff impulse state • mechanicalField state

theorem compactField_contDiff (impulse : ℝ) : ContDiff ℝ 1 (compactField impulse) :=
  (cutoff impulse).contDiff.smul mechanicalField_contDiff

theorem compactField_support (impulse : ℝ) : HasCompactSupport (compactField impulse) :=
  (cutoff impulse).hasCompactSupport.smul_right

structure MechanicalFlow (impulse : ℝ) where
  curve : ℝ → Mechanical
  starts : curve 0 = initialMechanical impulse
  evolves : ∀ time, HasDerivAt curve (compactField impulse (curve time)) time

theorem mechanicalFlow_exists (impulse : ℝ) : Nonempty (MechanicalFlow impulse) := by
  obtain ⟨curve, starts, evolves⟩ := compactField_global (compactField impulse)
    (compactField_contDiff impulse) (compactField_support impulse) (initialMechanical impulse)
  exact ⟨⟨curve, starts, evolves⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global
