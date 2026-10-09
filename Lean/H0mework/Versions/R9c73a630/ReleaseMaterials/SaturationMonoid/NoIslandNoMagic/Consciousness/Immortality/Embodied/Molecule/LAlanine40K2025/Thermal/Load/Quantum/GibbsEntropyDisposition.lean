import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Quantum.QuantumSubadditivity
import H0mework.Chemistry.LAlanineEntropy.QuantumGibbsBound
import H0mework.Chemistry.LAlanineEntropy.SpectralTensorEntropy

/-! # Entropy disposition of a Gibbs-initial joint under its actual unitary

The complete output joint supplies both reduced states, their mutual information,
and the environment Gibbs excess. Their sum equals system entropy change plus
inverse-temperature-weighted environment energy change, without an energy-balance premise.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Quantum

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Quantum
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population
open scoped ComplexOrder ENNReal

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Nonempty κ]

/-- The environment is prepared once from its registered energies and inverse temperature. -/
def gibbsEnvironment (energies : κ → ℝ) (beta : ℝ) : Matrix κ κ ℂ :=
  Matrix.diagonal (fun a => ((gibbsPMF energies beta a).toReal : ℂ))

theorem gibbsEnvironment_posSemidef (energies : κ → ℝ) (beta : ℝ) :
    (gibbsEnvironment energies beta).PosSemidef := diagonal_pmf_positive _

theorem gibbsEnvironment_trace (energies : κ → ℝ) (beta : ℝ) :
    (gibbsEnvironment energies beta).trace = 1 := diagonal_pmf_trace _

/-- The supplied actual unitary acts on the entire system/environment input. -/
def unitaryGibbsJoint (rho : Matrix ι ι ℂ) (energies : κ → ℝ) (beta : ℝ)
    (U : Matrix.unitaryGroup (ι × κ) ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  conjugation U (Matrix.kronecker rho (gibbsEnvironment energies beta))

theorem unitaryGibbsJoint_posSemidef (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (energies : κ → ℝ) (beta : ℝ) (U : Matrix.unitaryGroup (ι × κ) ℂ) :
    (unitaryGibbsJoint rho energies beta U).PosSemidef :=
  conjugation_posSemidef U _ (positive.kronecker (gibbsEnvironment_posSemidef energies beta))

theorem unitaryGibbsJoint_trace (rho : Matrix ι ι ℂ) (normalized : rho.trace = 1)
    (energies : κ → ℝ) (beta : ℝ) (U : Matrix.unitaryGroup (ι × κ) ℂ) :
    (unitaryGibbsJoint rho energies beta U).trace = 1 := by
  unfold unitaryGibbsJoint
  rw [conjugation_trace]
  dsimp only [Matrix.kronecker]
  rw [Matrix.trace_kronecker, normalized, gibbsEnvironment_trace, mul_one]

variable (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) (normalized : rho.trace = 1)
  (energies : κ → ℝ) (beta : ℝ) (U : Matrix.unitaryGroup (ι × κ) ℂ)

private abbrev joint := unitaryGibbsJoint rho energies beta U
private abbrev jointPositive := unitaryGibbsJoint_posSemidef rho positive energies beta U
private abbrev jointTrace := unitaryGibbsJoint_trace rho normalized energies beta U

/-- Both output spectra are read from the same actual joint. -/
def jointMutualInformation : ℝ :=
  spectralEntropy (systemReduce (joint rho energies beta U))
      (systemReduce_posSemidef _ (jointPositive rho positive energies beta U))
      ((systemReduce_trace _).trans (jointTrace rho normalized energies beta U)) +
    spectralEntropy (controllerReduce (joint rho energies beta U))
      (controllerReduce_posSemidef _ (jointPositive rho positive energies beta U))
      ((controllerReduce_trace _).trans (jointTrace rho normalized energies beta U)) -
    spectralEntropy (joint rho energies beta U) (jointPositive rho positive energies beta U)
      (jointTrace rho normalized energies beta U)

/-- Environment energy gain is measured against the single initial Gibbs preparation. -/
def environmentEnergyChange : ℝ :=
  Collision.energy (Matrix.diagonal (fun a => (energies a : ℂ)))
      (controllerReduce (joint rho energies beta U)) - meanEnergy energies (gibbsPMF energies beta)

/-- The environment's full spectral entropy, including coherence, enters its Gibbs excess. -/
def environmentGibbsExcess : ℝ :=
  beta * environmentEnergyChange rho energies beta U -
    (spectralEntropy (controllerReduce (joint rho energies beta U))
      (controllerReduce_posSemidef _ (jointPositive rho positive energies beta U))
      ((controllerReduce_trace _).trans (jointTrace rho normalized energies beta U)) -
        entropy (gibbsPMF energies beta))

/-- System entropy change plus weighted actual environment energy change. -/
def entropyProduction : ℝ :=
  spectralEntropy (systemReduce (joint rho energies beta U))
      (systemReduce_posSemidef _ (jointPositive rho positive energies beta U))
      ((systemReduce_trace _).trans (jointTrace rho normalized energies beta U)) -
    spectralEntropy rho positive normalized + beta * environmentEnergyChange rho energies beta U

/-- Tensor entropy and unitary invariance are generated from the input matrices and actual U. -/
theorem unitaryGibbsJoint_entropy :
    spectralEntropy (unitaryGibbsJoint rho energies beta U)
      (unitaryGibbsJoint_posSemidef rho positive energies beta U)
      (unitaryGibbsJoint_trace rho normalized energies beta U) =
        spectralEntropy rho positive normalized + entropy (gibbsPMF energies beta) := by
  have initialTrace : (Matrix.kronecker rho (gibbsEnvironment energies beta)).trace = 1 := by
    dsimp only [Matrix.kronecker]
    rw [Matrix.trace_kronecker, normalized, gibbsEnvironment_trace, mul_one]
  have invariant := spectralEntropy_unitary_conjugation
    (Matrix.kronecker rho (gibbsEnvironment energies beta))
    (positive.kronecker (gibbsEnvironment_posSemidef energies beta)) initialTrace U
  have additive := spectralEntropy_kronecker rho (gibbsEnvironment energies beta) positive
    (gibbsEnvironment_posSemidef energies beta) normalized (gibbsEnvironment_trace energies beta)
  exact invariant.trans (additive.trans (congrArg (_ + ·) (spectralEntropy_diagonal _)))

/-- The entropy balance is an identity of the same unitary-generated output and both marginals. -/
theorem entropyProduction_eq_mutual_add_gibbs :
    entropyProduction rho positive normalized energies beta U =
      jointMutualInformation rho positive normalized energies beta U +
        environmentGibbsExcess rho positive normalized energies beta U := by
  unfold entropyProduction jointMutualInformation environmentGibbsExcess
  rw [unitaryGibbsJoint_entropy rho positive normalized energies beta U]
  ring

variable [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

theorem jointMutualInformation_nonnegative :
    0 ≤ jointMutualInformation rho positive normalized energies beta U :=
  sub_nonneg.mpr (quantum_entropy_subadditive _
    (jointPositive rho positive energies beta U) (jointTrace rho normalized energies beta U))

omit [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem environmentGibbsExcess_nonnegative :
    0 ≤ environmentGibbsExcess rho positive normalized energies beta U :=
  quantumGibbs_freeEnergy_nonnegative energies beta _
    (controllerReduce_posSemidef _ (jointPositive rho positive energies beta U))
    ((controllerReduce_trace _).trans (jointTrace rho normalized energies beta U))

/-- The actual Gibbs-initial unitary joint pays correlation and disturbed-environment entropy. -/
theorem entropyProduction_nonnegative :
    0 ≤ entropyProduction rho positive normalized energies beta U := by
  rw [entropyProduction_eq_mutual_add_gibbs]
  exact add_nonneg (jointMutualInformation_nonnegative rho positive normalized energies beta U)
    (environmentGibbsExcess_nonnegative rho positive normalized energies beta U)

end

end LAlanine40K2025.Thermal.Load.Quantum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
