import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BranchMean
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Producer.SourceGeneratedPointerFeedback

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback
namespace SourceGeneratedConditionalWork

open Collision Quantum Propagation.Producer
open Load.Producer.HeatProbability
open scoped Matrix ComplexOrder

noncomputable section

private theorem pointer_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (normalized : joint.trace = 1) :
    zeroRead joint + oneRead joint = 1 := by
  have weights := congrArg Complex.re normalized
  unfold Matrix.trace at weights
  rw [Fintype.sum_sum_type] at weights
  exact weights

private theorem energy_sub_right {ι : Type*} [Fintype ι]
    (observable left right : Matrix ι ι ℂ) :
    energy observable (left - right) = energy observable left - energy observable right := by
  simp only [energy, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

private theorem weighted_energy_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H₀ H₁ H A B : Matrix ι ι ℂ) (p₀ p₁ : ℝ) (weights : p₀ + p₁ = 1) :
    energy H₀ A + energy H₁ B - energy H (A + B) =
      p₀ * energy H₀ (A + B) + p₁ * energy H₁ (A + B) - energy H (A + B) +
        energy (H₀ - H₁) ((p₁ : ℂ) • A - (p₀ : ℂ) • B) := by
  simp only [energy_sub_right, energy_smul_right, energy_sub_left, energy_add_right]
  rw [show p₁ = 1 - p₀ by linarith]
  ring

private theorem balanced_blocks {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (p₀ p₁ : ℝ) (weights : p₀ + p₁ = 1) :
    (p₀ : ℂ) • (A + B) + ((p₁ : ℂ) • A - (p₀ : ℂ) • B) = A ∧
      (p₁ : ℂ) • (A + B) - ((p₁ : ℂ) • A - (p₀ : ℂ) • B) = B := by
  have other : p₁ = 1 - p₀ := by linarith
  constructor <;> ext i j <;>
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  all_goals rw [other]; push_cast; ring

private theorem balanced_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (positive : joint.PosSemidef) :
    ((oneRead joint : ℂ) • joint.toBlocks₁₁ - (zeroRead joint : ℂ) • joint.toBlocks₂₂).trace = 0 := by
  have left : joint.toBlocks₁₁.trace = (zeroRead joint : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp ((positive.submatrix Sum.inl).trace_nonneg)).2.symm
  have right : joint.toBlocks₂₂.trace = (oneRead joint : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp ((positive.submatrix Sum.inr).trace_nonneg)).2.symm
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, left, right]
  change (oneRead joint : ℂ) * zeroRead joint - (zeroRead joint : ℂ) * oneRead joint = 0
  ring

def loadObservable : Current.FullJoint :=
  conjugation (star (Current.loadPulse (nativeClockStep : ℝ))) Physical.baselineHamiltonian

def supplyObservable : Current.FullJoint :=
  conjugation (star (freePhase (nativeClockStep : ℝ) • Current.pulse (nativeClockStep : ℝ)))
    Physical.baselineHamiltonian

def contrast : Current.FullJoint := loadObservable - supplyObservable

def balancedResidual (current : Live.State) : Current.FullJoint :=
  (oneRead current.joint : ℂ) • current.joint.toBlocks₁₁ -
    (zeroRead current.joint : ℂ) • current.joint.toBlocks₂₂

def signedDefect (current : Live.State) : ℝ := energy contrast (balancedResidual current)

def marginalPrediction (current : Live.State) : ℝ :=
  zeroRead current.joint * energy loadObservable (bodyRead current.joint) +
    oneRead current.joint * energy supplyObservable (bodyRead current.joint) -
      energy Physical.baselineHamiltonian (bodyRead current.joint)

theorem weights_sum (current : Live.State) : zeroRead current.joint + oneRead current.joint = 1 :=
  pointer_weights current.joint current.normalized

theorem blocks_reconstruction (current : Live.State) :
    (zeroRead current.joint : ℂ) • bodyRead current.joint + balancedResidual current = current.joint.toBlocks₁₁ ∧
      (oneRead current.joint : ℂ) • bodyRead current.joint - balancedResidual current = current.joint.toBlocks₂₂ :=
  balanced_blocks current.joint.toBlocks₁₁ current.joint.toBlocks₂₂
    (zeroRead current.joint) (oneRead current.joint) (weights_sum current)

theorem balancedResidual_trace (current : Live.State) : (balancedResidual current).trace = 0 :=
  balanced_trace current.joint current.positive

theorem energy_dual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (observable state : Matrix ι ι ℂ) (unitary : Matrix.unitaryGroup ι ℂ) :
    energy observable (conjugation unitary state) = energy (conjugation (star unitary) observable) state := by
  have original := Work.Capacity.energy_unitary_conjugation observable (conjugation unitary state) (star unitary)
  have returned : conjugation (star unitary) (conjugation unitary state) = state := by
    change Unitary.conjStarAlgAut ℂ _ (star unitary) (Unitary.conjStarAlgAut ℂ _ unitary state) = state
    rw [← Unitary.conjStarAlgAut_symm]
    exact StarAlgEquiv.symm_apply_apply _ state
  change energy (conjugation (star unitary) observable) (conjugation (star unitary) (conjugation unitary state)) = _ at original
  rw [returned] at original
  exact original.symm

theorem conjugation_hermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (unitary : Matrix.unitaryGroup ι ℂ) (observable : Matrix ι ι ℂ)
    (hermitian : observable.IsHermitian) : (conjugation unitary observable).IsHermitian := by
  change star (conjugation unitary observable) = conjugation unitary observable
  simp only [conjugation_apply, star_mul, star_star, hermitian.star_eq, Matrix.mul_assoc]

theorem contrast_hermitian : contrast.IsHermitian :=
  (conjugation_hermitian _ _ oldBaseline_hermitian).sub
    (conjugation_hermitian _ _ oldBaseline_hermitian)

theorem signed_defect_blocks (current : Live.State) :
    signedDefect current =
      oneRead current.joint * energy contrast current.joint.toBlocks₁₁ -
        zeroRead current.joint * energy contrast current.joint.toBlocks₂₂ :=
  (energy_sub_right contrast _ _).trans
    (congrArg₂ (· - ·) (energy_smul_right contrast _ (oneRead current.joint))
      (energy_smul_right contrast _ (zeroRead current.joint)))

theorem work_of_response (current : Live.State)
    (response : type_of% (respondNext_observable Physical.baselineHamiltonian current))
    (work : type_of% (responseWork_body current)) :
    responseWork current = marginalPrediction current + signedDefect current := by
  have actual := work.trans
    (congrArg (· - energy Physical.baselineHamiltonian (bodyRead current.joint))
      (response.trans
        (congrArg₂ (· + ·) (energy_dual _ _ _) (energy_dual _ _ _))))
  exact actual.trans (weighted_energy_split loadObservable supplyObservable Physical.baselineHamiltonian
    current.joint.toBlocks₁₁ current.joint.toBlocks₂₂
    (zeroRead current.joint) (oneRead current.joint) (weights_sum current))

theorem original_work (current : Live.State) :
    responseWork current = marginalPrediction current + signedDefect current :=
  work_of_response current (respondNext_observable Physical.baselineHamiltonian current) (responseWork_body current)

theorem original_account (current : Live.State) :
    (Live.freeEnergy (respondNext current) - Live.freeEnergy current) +
      (Live.entropyProduction (respondNext current) - Live.entropyProduction current) =
        marginalPrediction current + signedDefect current :=
  (respondNext_netAccount current).trans (original_work current)

end
end SourceGeneratedConditionalWork
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
