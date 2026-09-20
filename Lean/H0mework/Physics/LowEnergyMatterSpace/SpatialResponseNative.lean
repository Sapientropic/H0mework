import H0mework.Physics.LowEnergyMatterSpace.SpatialResponseKubo

/-! The complete first current response is a bounded spatial observable read by the original source. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
open Stage9DEF
noncomputable section

def responseOperator (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (current : MatterL2 →L[ℂ] MatterL2) (t : ℝ) :
    MatterL2 →L[ℂ] MatterL2 :=
  (firstOrderOperator perturbation continuousPerturbation t).adjoint * current * freeOperator t+
    (freeOperator t).adjoint * current * firstOrderOperator perturbation continuousPerturbation t

theorem responseOperator_pair (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (current : MatterL2 →L[ℂ] MatterL2) (u : MatterL2) (t : ℝ) :
    inner ℂ u (responseOperator perturbation continuousPerturbation current t u)=
      currentVariation perturbation current u t := by
  change inner ℂ u ((firstOrderOperator perturbation continuousPerturbation t).adjoint
      (current (freeOperator t u))+(freeOperator t).adjoint
      (current (firstOrderOperator perturbation continuousPerturbation t u)))=_
  rw [inner_add_right,ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem responseOperator_selfAdjoint (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (current : MatterL2 →L[ℂ] MatterL2)
    (hermitian : IsSelfAdjoint current) (t : ℝ) :
    IsSelfAdjoint (responseOperator perturbation continuousPerturbation current t) := by
  change star ((star (firstOrderOperator perturbation continuousPerturbation t)*current*freeOperator t)+
    (star (freeOperator t)*current*firstOrderOperator perturbation continuousPerturbation t))=_
  simp only [star_add,star_mul,star_star,hermitian.star_eq,mul_assoc]
  exact add_comm _ _

def pathOperator (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (t epsilon : ℝ) : MatterL2 →L[ℂ] MatterL2 :=
  freeOperator t+epsilon • firstOrderOperator perturbation continuousPerturbation t

def pathObservable (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (current : MatterL2 →L[ℂ] MatterL2) (t epsilon : ℝ) :
    MatterL2 →L[ℂ] MatterL2 :=
  (pathOperator perturbation continuousPerturbation t epsilon).adjoint.comp
    (current.comp (pathOperator perturbation continuousPerturbation t epsilon))

theorem pathObservable_pair (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (current : MatterL2 →L[ℂ] MatterL2)
    (u : MatterL2) (t epsilon : ℝ) :
    inner ℂ u (pathObservable perturbation continuousPerturbation current t epsilon u)=
      inner ℂ (epsilonPath perturbation u t epsilon) (current (epsilonPath perturbation u t epsilon)) := by
  change inner ℂ u ((pathOperator perturbation continuousPerturbation t epsilon).adjoint
    (current (pathOperator perturbation continuousPerturbation t epsilon u)))=_
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem native_response (preparation : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousPreparation : Continuous preparation) (preparedAt : ℝ)
    (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2) (continuousPerturbation : Continuous perturbation)
    (current : MatterL2 →L[ℂ] MatterL2) (t : ℝ) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
        (normalizedPreparationNative preparation continuousPreparation preparedAt
          (responseOperator perturbation continuousPerturbation current t))))=
      currentVariation perturbation current (normalizedPreparation preparation continuousPreparation preparedAt) t := by
  rw [normalizedPreparationNative_sourceResponse]
  exact responseOperator_pair perturbation continuousPerturbation current _ t

theorem native_kubo (preparation : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousPreparation : Continuous preparation) (preparedAt : ℝ)
    (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2) (continuousPerturbation : Continuous perturbation)
    (hermitian : ∀ s, IsSelfAdjoint (perturbation s)) (current : MatterL2 →L[ℂ] MatterL2) (t : ℝ) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
        (normalizedPreparationNative preparation continuousPreparation preparedAt
          (responseOperator perturbation continuousPerturbation current t))))=
      Complex.I*∫ s in (0 : ℝ)..t,
        kuboKernel perturbation current (normalizedPreparation preparation continuousPreparation preparedAt) t s := by
  rw [native_response,currentVariation_kubo perturbation continuousPerturbation hermitian]

theorem native_epsilon_current (preparation : ℝ → MatterFiber →L[ℂ] MatterL2)
    (continuousPreparation : Continuous preparation) (preparedAt : ℝ)
    (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2) (continuousPerturbation : Continuous perturbation)
    (current : MatterL2 →L[ℂ] MatterL2) (t : ℝ) :
    HasDerivAt (fun epsilon => State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
        (normalizedPreparationNative preparation continuousPreparation preparedAt
          (pathObservable perturbation continuousPerturbation current t epsilon)))))
      (currentVariation perturbation current (normalizedPreparation preparation continuousPreparation preparedAt) t) 0 := by
  have same (epsilon : ℝ) : State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
        (normalizedPreparationNative preparation continuousPreparation preparedAt
          (pathObservable perturbation continuousPerturbation current t epsilon))))=
      inner ℂ (epsilonPath perturbation (normalizedPreparation preparation continuousPreparation preparedAt) t epsilon)
        (current (epsilonPath perturbation (normalizedPreparation preparation continuousPreparation preparedAt) t epsilon)) := by
    rw [normalizedPreparationNative_sourceResponse]
    exact pathObservable_pair perturbation continuousPerturbation current _ t epsilon
  simp_rw [same]
  exact epsilonCurrent_derivative perturbation current _ t

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
