import H0mework.Chemistry.LAlanineThermalDynamics.PairHamiltonian
import H0mework.Chemistry.LAlanineEntropy.SpectralEntropyInvariance

/-!
# The pair flow acts on the retained joint, including its correlations

The input is the current matrix, not freshly prepared marginals. Positivity,
normalization and spectral entropy are carried to its generated successor.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Dynamics

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Collision
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Quantum
open scoped Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

def pairAdvance (H : SystemMatrix ι) (g time : ℝ) (current : JointMatrix ι) : JointMatrix ι :=
  pairPropagatorMatrix H g time * current * pairPropagatorMatrix H g (-time)

theorem pairAdvance_eq_unitary (H : SystemMatrix ι) (hH : H.IsHermitian)
    (g time : ℝ) (current : JointMatrix ι) :
    pairAdvance H g time current =
      (pairUnitary H hH g time : JointMatrix ι) * current *
        star (pairUnitary H hH g time : JointMatrix ι) := by
  unfold pairAdvance
  rw [pairPropagatorMatrix_neg_eq_star H hH]
  rfl

theorem pairAdvance_posSemidef (H : SystemMatrix ι) (hH : H.IsHermitian)
    (g time : ℝ) (current : JointMatrix ι) (positive : current.PosSemidef) :
    (pairAdvance H g time current).PosSemidef := by
  rw [pairAdvance_eq_unitary H hH]
  exact positive.mul_mul_conjTranspose_same (pairUnitary H hH g time : JointMatrix ι)

theorem pairAdvance_trace (H : SystemMatrix ι) (hH : H.IsHermitian)
    (g time : ℝ) (current : JointMatrix ι) :
    (pairAdvance H g time current).trace = current.trace := by
  rw [pairAdvance_eq_unitary H hH]
  exact unitary_conjugate_trace current (pairUnitary H hH g time)

theorem pairAdvance_normalized (H : SystemMatrix ι) (hH : H.IsHermitian)
    (g time : ℝ) (current : JointMatrix ι) (normalized : current.trace = 1) :
    (pairAdvance H g time current).trace = 1 :=
  (pairAdvance_trace H hH g time current).trans normalized

theorem pairAdvance_spectralEntropy (H : SystemMatrix ι) (hH : H.IsHermitian)
    (g time : ℝ) (current : JointMatrix ι) (positive : current.PosSemidef)
    (normalized : current.trace = 1) :
    spectralEntropy (pairAdvance H g time current)
      (pairAdvance_posSemidef H hH g time current positive)
      (pairAdvance_normalized H hH g time current normalized) =
      spectralEntropy current positive normalized := by
  apply spectralEntropy_eq_of_charpoly
  rw [pairAdvance_eq_unitary H hH, Matrix.charpoly_mul_comm,
    ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]

theorem pairPropagatorMatrix_commute (H : SystemMatrix ι) (g time : ℝ)
    (observable : JointMatrix ι) (commutes : Commute observable (pairH H g)) :
    Commute observable (pairPropagatorMatrix H g time) := by
  apply Commute.of_map (pairMatrixOperatorEquiv (ι := ι)).injective
  change Commute (pairMatrixOperatorEquiv observable)
    (pairMatrixOperatorEquiv (pairMatrixOperatorEquiv.symm (pairPropagator H g time)))
  rw [StarAlgEquiv.apply_symm_apply]
  exact (((commutes.map pairMatrixOperatorEquiv).smul_right (-Complex.I)).smul_right
    (time : ℂ)).exp_right

theorem pairAdvance_conserved_of_commute (H : SystemMatrix ι) (hH : H.IsHermitian)
    (g time : ℝ) (observable current : JointMatrix ι)
    (commutes : Commute observable (pairH H g)) :
    Matrix.trace (observable * pairAdvance H g time current) =
      Matrix.trace (observable * current) := by
  have commutesU := (pairPropagatorMatrix_commute H g time observable commutes).eq
  have rearrange : observable * (pairPropagatorMatrix H g time * current *
      star (pairPropagatorMatrix H g time)) =
      pairPropagatorMatrix H g time * (observable * current) *
        star (pairPropagatorMatrix H g time) := by
    calc
      _ = (observable * pairPropagatorMatrix H g time) * current *
          star (pairPropagatorMatrix H g time) := by simp only [Matrix.mul_assoc]
      _ = (pairPropagatorMatrix H g time * observable) * current *
          star (pairPropagatorMatrix H g time) := by rw [commutesU]
      _ = _ := by simp only [Matrix.mul_assoc]
  unfold pairAdvance
  rw [pairPropagatorMatrix_neg_eq_star H hH, rearrange]
  exact unitary_conjugate_trace (observable * current) (pairUnitary H hH g time)

theorem pairAdvance_bareEnergy (H : SystemMatrix ι) (hH : H.IsHermitian)
    (g time : ℝ) (current : JointMatrix ι) :
    Matrix.trace (freePairH H * pairAdvance H g time current) =
      Matrix.trace (freePairH H * current) :=
  pairAdvance_conserved_of_commute H hH g time _ current (freePairH_commute_pairH H g)

theorem pairAdvance_interactionEnergy (H : SystemMatrix ι) (hH : H.IsHermitian)
    (g time : ℝ) (current : JointMatrix ι) :
    Matrix.trace (((g : ℂ) • swapOperator) * pairAdvance H g time current) =
      Matrix.trace (((g : ℂ) • swapOperator) * current) :=
  pairAdvance_conserved_of_commute H hH g time _ current (interaction_commute_pairH H g)

theorem pairAdvance_totalEnergy (H : SystemMatrix ι) (hH : H.IsHermitian)
    (g time : ℝ) (current : JointMatrix ι) :
    Matrix.trace (pairH H g * pairAdvance H g time current) =
      Matrix.trace (pairH H g * current) :=
  pairAdvance_conserved_of_commute H hH g time _ current (Commute.refl _)

theorem pairPropagatorMatrix_add (H : SystemMatrix ι) (hH : H.IsHermitian) (g time next : ℝ) :
    pairPropagatorMatrix H g (time + next) =
      pairPropagatorMatrix H g time * pairPropagatorMatrix H g next := by
  unfold pairPropagatorMatrix
  rw [pairPropagator_add H hH]
  exact map_mul (pairMatrixOperatorEquiv (ι := ι)).symm _ _

@[simp] theorem pairAdvance_zero (H : SystemMatrix ι) (hH : H.IsHermitian)
    (g : ℝ) (current : JointMatrix ι) : pairAdvance H g 0 current = current := by
  simp only [pairAdvance, neg_zero, pairPropagatorMatrix, pairPropagator_zero H hH]
  rw [map_one (pairMatrixOperatorEquiv (ι := ι)).symm, Matrix.one_mul, Matrix.mul_one]

/-- A generated target is consumed directly by the same flow, without a product reset. -/
theorem pairAdvance_add (H : SystemMatrix ι) (hH : H.IsHermitian)
    (g time next : ℝ) (current : JointMatrix ι) :
    pairAdvance H g (time + next) current =
      pairAdvance H g time (pairAdvance H g next current) := by
  have backward : pairPropagatorMatrix H g (-(time + next)) =
      pairPropagatorMatrix H g (-next) * pairPropagatorMatrix H g (-time) := by
    rw [neg_add, add_comm, pairPropagatorMatrix_add H hH]
  simp only [pairAdvance, pairPropagatorMatrix_add H hH, backward, Matrix.mul_assoc]

end

end LAlanine40K2025.Thermal.Dynamics
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
