import H0mework.Versions.X.Fock.CopyGraph.TimeGramMoments

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeGram

open SourceCopyProgram (Index scale)
open SourceCopyTimeModel (hilbert mass)
open scoped Classical
noncomputable section

theorem gram_hilbert (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    hilbert (gram depth index value) = hilbert value := rfl

theorem gram_clock (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    SourceJointClockGraph.clock (gram depth index value) =
      ((meanPhase depth index : ℂ) * mass value + SourceJointClockGraph.clock value) / (scale depth index : ℂ) := by
  have cardinal : (Fintype.card (Fin (index.val + 1)) : ℂ) = (scale depth index : ℂ) := by
    rw [Fintype.card_fin, SourceCopyProgram.scale_source]
  change (∑ phase : Fin (index.val + 1), (scale depth index : ℂ)⁻¹ *
    ((scale depth index : ℂ)⁻¹ * (SourceJointClockGraph.clock value + (phase.val : ℂ) * mass value))) = _
  have expanded : ∀ phase : Fin (index.val + 1), (scale depth index : ℂ)⁻¹ *
      ((scale depth index : ℂ)⁻¹ * (SourceJointClockGraph.clock value + (phase.val : ℂ) * mass value)) =
      (scale depth index : ℂ)⁻¹ ^ 2 * SourceJointClockGraph.clock value +
        (scale depth index : ℂ)⁻¹ ^ 2 * (phase.val : ℂ) * mass value := by intro phase;ring
  simp only [expanded, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, cardinal, phase_sum_complex]
  field_simp [SourceCopyGraph.scale_nonzero depth index]
  ring

theorem gram_mass (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    mass (gram depth index value) = (normalizer depth index : ℂ) * mass value +
      (meanPhase depth index : ℂ) *
        (((meanPhase depth index : ℂ) * mass value + SourceJointClockGraph.clock value) / (scale depth index : ℂ)) := by
  have cardinal : (Fintype.card (Fin (index.val + 1)) : ℂ) = (scale depth index : ℂ) := by
    rw [Fintype.card_fin, SourceCopyProgram.scale_source]
  change (∑ phase : Fin (index.val + 1), (mass value + ((phase.val : ℂ) / (scale depth index : ℂ)) *
    ((scale depth index : ℂ)⁻¹ * (SourceJointClockGraph.clock value + (phase.val : ℂ) * mass value)))) = _
  have expanded : ∀ phase : Fin (index.val + 1),
      mass value + ((phase.val : ℂ) / (scale depth index : ℂ)) *
        ((scale depth index : ℂ)⁻¹ * (SourceJointClockGraph.clock value + (phase.val : ℂ) * mass value)) =
      mass value + (scale depth index : ℂ)⁻¹ ^ 2 * (phase.val : ℂ) * SourceJointClockGraph.clock value +
        (scale depth index : ℂ)⁻¹ ^ 2 * (phase.val : ℂ) ^ 2 * mass value := by
    intro phase
    simp only [div_eq_mul_inv]
    ring
  simp only [expanded, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, cardinal, phase_sum_complex, square_sum_complex]
  rw [normalizer_complex]
  field_simp [SourceCopyGraph.scale_nonzero depth index]
  ring

def solve (depth : Nat) (index : Index depth) (forcing : SourceJointClockGraph.Carrier) : SourceJointClockGraph.Carrier :=
  let recoveredMass := (mass forcing - (meanPhase depth index : ℂ) * SourceJointClockGraph.clock forcing) /
    (normalizer depth index : ℂ)
  WithLp.toLp 2 (WithLp.toLp 2 (hilbert forcing, recoveredMass),
    (scale depth index : ℂ) * SourceJointClockGraph.clock forcing - (meanPhase depth index : ℂ) * recoveredMass)

theorem solve_clock (depth : Nat) (index : Index depth) (forcing : SourceJointClockGraph.Carrier) :
    SourceJointClockGraph.clock (gram depth index (solve depth index forcing)) = SourceJointClockGraph.clock forcing := by
  rw [gram_clock]
  change ((meanPhase depth index : ℂ) *
    ((mass forcing - (meanPhase depth index : ℂ) * SourceJointClockGraph.clock forcing) / (normalizer depth index : ℂ)) +
    ((scale depth index : ℂ) * SourceJointClockGraph.clock forcing - (meanPhase depth index : ℂ) *
      ((mass forcing - (meanPhase depth index : ℂ) * SourceJointClockGraph.clock forcing) / (normalizer depth index : ℂ)))) /
      (scale depth index : ℂ) = _
  convert mul_div_cancel_left₀ (SourceJointClockGraph.clock forcing) (SourceCopyGraph.scale_nonzero depth index) using 1
  ring

theorem solve_mass (depth : Nat) (index : Index depth) (forcing : SourceJointClockGraph.Carrier) :
    mass (gram depth index (solve depth index forcing)) = mass forcing := by
  rw [gram_mass, ← gram_clock, solve_clock]
  change (normalizer depth index : ℂ) *
    ((mass forcing - (meanPhase depth index : ℂ) * SourceJointClockGraph.clock forcing) / (normalizer depth index : ℂ)) +
      (meanPhase depth index : ℂ) * SourceJointClockGraph.clock forcing = mass forcing
  rw [mul_div_cancel₀ _ (normalizer_nonzero depth index), sub_add_cancel]

theorem solve_equation (depth : Nat) (index : Index depth) (forcing : SourceJointClockGraph.Carrier) :
    (analysis depth index).adjoint (analysis depth index (solve depth index forcing)) = forcing := by
  rw [gram_source]
  apply (WithLp.linearEquiv 2 ℂ (SourceMassCompletion.Joint × ℂ)).injective
  apply Prod.ext
  · apply (WithLp.linearEquiv 2 ℂ (SourceOwnedObservationHistory.SourceShift.H × ℂ)).injective
    exact Prod.ext rfl (solve_mass depth index forcing)
  · exact solve_clock depth index forcing

end
end SourceCopyTimeGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
