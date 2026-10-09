import H0mework.Chemistry.LAlanineTrueTube.DynamicsStep
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.TraceSignedField
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.ChecksIncidence
import H0mework.Versions.R9c73a630.Chemistry.LAlanineGradient.Bounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeContinuation

open SourceGaussianModel ContinuousGradient TrueTubeSource TrueTubeTrace Set Metric ODE
open scoped NNReal
noncomputable section

def cubeLower : Point := fun i => sourceCentre i - sourceRadius
def cubeUpper : Point := fun i => sourceCentre i + sourceRadius

theorem sourceCube_eq_Icc : sourceCube = Icc cubeLower cubeUpper := by
  ext x
  change (∀ i, |x i - sourceCentre i| ≤ sourceRadius) ↔ _
  constructor
  · intro h
    constructor <;> intro i <;> have hi := abs_le.mp (h i) <;>
      change _ ≤ _ <;> dsimp [cubeLower, cubeUpper] <;> linarith
  · intro h i
    have lo := h.1 i
    have hi := h.2 i
    dsimp [cubeLower, cubeUpper] at lo hi
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem cube_ordered : cubeLower ≤ cubeUpper := by
  intro i
  dsimp [cubeLower, cubeUpper]
  linarith [sourceRadius_positive]

def globalField (d : Direction) : Point → Point :=
  LAlanineTrueTube.Dynamics.extension cubeLower cubeUpper (signedGradient (sign d))

theorem signed_on_cube (d : Direction) :
    LipschitzOnWith sourceLipschitzBound (signedGradient (sign d)) (Icc cubeLower cubeUpper) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have unit : |(sign d : ℝ)| = 1 := by exact_mod_cast (TrueTubeChecks.direction_units d).1
  rw [← sourceCube_eq_Icc] at hx hy
  simpa only [signedGradient, dist_smul₀, Real.norm_eq_abs, unit, one_mul] using
    sourceGradient_lipschitzOn_cube.dist_le_mul x hx y hy

theorem globalField_lipschitz (d : Direction) : LipschitzWith sourceLipschitzBound (globalField d) :=
  LAlanineTrueTube.Dynamics.extension_lipschitz cubeLower cubeUpper cube_ordered _ _ (signed_on_cube d)

theorem globalField_eq_original (d : Direction) (x : Point) (inside : x ∈ sourceCube) :
    globalField d x = signedGradient (sign d) x := by
  unfold globalField LAlanineTrueTube.Dynamics.extension
  rw [LAlanineTrueTube.Dynamics.clip_eq _ _ _ (sourceCube_eq_Icc ▸ inside)]

theorem signed_speed_bounds (d : Direction) (x : Point) (inside : x ∈ Icc cubeLower cubeUpper) :
    signedGradient (sign d) x ∈ Icc (fun _ => -(sourceSpeedBound : ℝ)) (fun _ => (sourceSpeedBound : ℝ)) := by
  have unit : |(sign d : ℝ)| = 1 := by exact_mod_cast (TrueTubeChecks.direction_units d).1
  have normBound : ‖signedGradient (sign d) x‖ ≤ (sourceSpeedBound : ℝ) := by
    simpa only [signedGradient, norm_smul, Real.norm_eq_abs, unit, one_mul] using
      sourceGradient_norm_le x (sourceCube_eq_Icc.symm ▸ inside)
  constructor <;> intro i
  · exact (abs_le.mp ((norm_le_pi_norm _ i).trans normBound)).1
  · exact (abs_le.mp ((norm_le_pi_norm _ i).trans normBound)).2

theorem exists_global_window (d : Direction) (initial : Point) :
    ∃ curve : ℝ → Point, curve 0 = initial ∧
      ∀ t ∈ Icc (0 : ℝ) (1 / 2),
        HasDerivWithinAt curve (globalField d (curve t)) (Icc (0 : ℝ) (1 / 2)) t := by
  have picard := LAlanineTrueTube.Dynamics.extension_picard cubeLower cubeUpper cube_ordered
    (signedGradient (sign d)) sourceLipschitzBound (signed_on_cube d)
    (fun _ => -(sourceSpeedBound : ℝ)) (fun _ => (sourceSpeedBound : ℝ))
    (signed_speed_bounds d) (1 / 2) (by norm_num) initial
  exact picard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

end
end LAlanine40K2025.BasinRefinement.TrueTubeContinuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
