import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.PerturbedVariation
import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.PerturbedPhysical
import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.SpatialResponseNative

/-! The Picard-generated finite-coupling current has the already-generated Kubo response as its derivative. -/
set_option autoImplicit false
open Set
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
open Stage9DEF
noncomputable section

private theorem current_pair_derivative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (curve : ℝ → E) (variation : E) (current : E →L[ℂ] E)
    (derivative : HasDerivAt curve variation 0) :
    HasDerivAt (fun epsilon => inner ℂ (curve epsilon) (current (curve epsilon)))
      (inner ℂ variation (current (curve 0))+inner ℂ (curve 0) (current variation)) 0 := by
  have paired := derivative.inner ℂ ((current.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 derivative)
  have applyCurrent (v : E) : (current.restrictScalars ℝ) v=current v := rfl
  simp only [Function.comp_apply,applyCurrent] at paired
  convert! paired using 1
  exact add_comm _ _

namespace PerturbedDevelopment
variable {perturbation : ℝ → MatterL2 →L[ℂ] MatterL2}
    (development : PerturbedDevelopment perturbation)

theorem coupling_derivative_at_zero (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ time, IsSelfAdjoint (perturbation time))
    (u : MatterL2) (time : ℝ) (inside : time ∈ Ioo (-development.radius) development.radius) :
    HasDerivAt (fun epsilon => development.physicalCurve epsilon 0 u time)
      (firstOrder perturbation time u) 0 := by
  have atZero : (0 : ℝ) ∈ Ioo (-development.radius) development.radius :=
    ⟨neg_lt_zero.mpr development.positive,development.positive⟩
  have generated := true_family_physical_derivative perturbation continuousPerturbation symmetric
    development.radius development.positive (fun epsilon s => development.curve epsilon 0 u s) u
    (fun epsilon coupling => development.starts epsilon 0 u coupling atZero)
    (fun epsilon coupling => development.evolves epsilon 0 u coupling atZero) time inside
  simpa only [physicalCurve,neg_zero,spatialUnitary_zero] using generated

theorem current_coupling_derivative (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ time, IsSelfAdjoint (perturbation time))
    (current : MatterL2 →L[ℂ] MatterL2) (u : MatterL2)
    (time : ℝ) (inside : time ∈ Ioo (-development.radius) development.radius) :
    HasDerivAt (fun epsilon => inner ℂ (development.physicalCurve epsilon 0 u time)
      (current (development.physicalCurve epsilon 0 u time)))
      (currentVariation perturbation current u time) 0 := by
  have atZero : (0 : ℝ) ∈ Ioo (-development.radius) development.radius :=
    ⟨neg_lt_zero.mpr development.positive,development.positive⟩
  have derivative := current_pair_derivative (fun epsilon => development.physicalCurve epsilon 0 u time)
    (firstOrder perturbation time u) current
    (development.coupling_derivative_at_zero continuousPerturbation symmetric u time inside)
  simpa only [development.physicalCurve_zeroCoupling symmetric 0 time atZero inside,sub_zero,currentVariation] using derivative

theorem current_coupling_kubo (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ time, IsSelfAdjoint (perturbation time))
    (current : MatterL2 →L[ℂ] MatterL2) (u : MatterL2)
    (time : ℝ) (inside : time ∈ Ioo (-development.radius) development.radius) :
    HasDerivAt (fun epsilon => inner ℂ (development.physicalCurve epsilon 0 u time)
      (current (development.physicalCurve epsilon 0 u time)))
      (Complex.I*∫ s in (0 : ℝ)..time, kuboKernel perturbation current u time s) 0 := by
  rw [← currentVariation_kubo perturbation continuousPerturbation symmetric]
  exact development.current_coupling_derivative continuousPerturbation symmetric current u time inside

theorem current_coupling_source (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ time, IsSelfAdjoint (perturbation time))
    (preparation : ℝ → MatterFiber →L[ℂ] MatterL2) (continuousPreparation : Continuous preparation)
    (preparedAt : ℝ) (current : MatterL2 →L[ℂ] MatterL2)
    (time : ℝ) (inside : time ∈ Ioo (-development.radius) development.radius) :
    HasDerivAt (fun epsilon => inner ℂ
      (development.physicalCurve epsilon 0 (normalizedPreparation preparation continuousPreparation preparedAt) time)
      (current (development.physicalCurve epsilon 0 (normalizedPreparation preparation continuousPreparation preparedAt) time)))
      (State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
        (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
          (normalizedPreparationNative preparation continuousPreparation preparedAt
            (responseOperator perturbation continuousPerturbation current time))))) 0 := by
  rw [native_response]
  exact development.current_coupling_derivative continuousPerturbation symmetric current _ time inside

end PerturbedDevelopment
end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
