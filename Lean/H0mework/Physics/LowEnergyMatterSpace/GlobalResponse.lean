import H0mework.Physics.LowEnergyMatterSpace.GlobalFlow
import H0mework.Physics.LowEnergyMatterSpace.PerturbedOperator

/-! Global source developments consume the existing Kubo and native response at every physical time. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
open SU7MotherLieAlgebra DiracCliffordRepresentation Stage9DEF
noncomputable section

namespace GlobalPerturbedDevelopment
variable {perturbation : ℝ → MatterL2 →L[ℂ] MatterL2}
    (development : GlobalPerturbedDevelopment perturbation)

private theorem time_inside (time : ℝ) : time ∈ Ioo (-(|time|+1)) (|time|+1) :=
  abs_lt.mp (by linarith)

private theorem window_positive (time : ℝ) : 0 < |time|+1 := by positivity

theorem physicalCurve_starts (epsilon start : ℝ) (initial : MatterL2) :
    development.physicalCurve epsilon start start initial=initial := by
  rw [physicalCurve,development.starts,← spatialUnitary_add,add_neg_cancel,spatialUnitary_zero]

theorem physicalCurve_weak (epsilon start : ℝ) (initial : MatterL2)
    (time : ℝ) (test : Quantum.Generator.domain spatialAction) :
    HasDerivAt (fun t => inner ℂ (test : MatterL2) (development.physicalCurve epsilon start t initial))
      (-Complex.I*inner ℂ (Quantum.Generator.hamiltonian spatialAction test)
          (development.physicalCurve epsilon start time initial)+
        inner ℂ (test : MatterL2) ((-Complex.I*(epsilon : ℂ)) •
          perturbation time (development.physicalCurve epsilon start time initial))) time :=
  perturbed_physical_weak perturbation epsilon time _ (development.evolves epsilon start _ time) test

theorem zeroPast (past : ∀ t≤0, perturbation t=0) (epsilon time : ℝ) (before : time≤0)
    (initial : MatterL2) : development.curve epsilon 0 initial time=initial := by
  have derivative (t : ℝ) (inside : t ∈ Icc time 0) :
      HasDerivAt (development.curve epsilon 0 initial) 0 t := by
    simpa [interactionGenerator,heisenberg,past t inside.2] using development.evolves epsilon 0 initial t
  have same := (convex_Icc time 0).norm_image_sub_le_of_norm_deriv_le (C := 0)
    (fun t inside => (derivative t inside).differentiableAt)
    (fun t inside => by simp only [(derivative t inside).deriv,norm_zero,le_refl])
    (left_mem_Icc.mpr before) (right_mem_Icc.mpr before)
  rw [development.starts,zero_mul] at same
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp same)).symm

theorem physicalCurve_zeroPast (past : ∀ t≤0, perturbation t=0) (epsilon time : ℝ) (before : time≤0)
    (initial : MatterL2) : development.physicalCurve epsilon 0 time initial=spatialUnitary time initial := by
  rw [physicalCurve,neg_zero,spatialUnitary_zero,development.zeroPast past epsilon time before]

theorem coupling_derivative (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) (initial : MatterL2) (time : ℝ) :
    HasDerivAt (fun epsilon => development.physicalCurve epsilon 0 time initial)
      (firstOrder perturbation time initial) 0 :=
  (development.window (|time|+1) (window_positive time)).coupling_derivative_at_zero
    continuousPerturbation symmetric initial time (time_inside time)

def physicalOperator (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) (epsilon start time : ℝ) :
    MatterL2 →L[ℂ] MatterL2 :=
  (development.physicalUnitary symmetric epsilon start time).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem physicalOperator_apply (symmetric : ∀ t, IsSelfAdjoint (perturbation t))
    (epsilon start time : ℝ) (initial : MatterL2) :
    development.physicalOperator symmetric epsilon start time initial=
      development.physicalCurve epsilon start time initial := rfl

theorem operator_derivative (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) (time : ℝ) :
    HasDerivAt (fun epsilon => development.physicalOperator symmetric epsilon 0 time)
      (firstOrderOperator perturbation continuousPerturbation time) 0 := by
  let localFlow := development.window (|time|+1) (window_positive time)
  have generated := localFlow.couplingOperator_derivative continuousPerturbation symmetric time (time_inside time)
  apply generated.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (by norm_num : (-1 : ℝ)<0) (by norm_num : (0 : ℝ)<1)] with epsilon near
  ext initial
  rw [localFlow.couplingOperator_apply symmetric time (time_inside time) epsilon (abs_le.mpr near)]
  rfl

theorem current_kubo (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) (current : MatterL2 →L[ℂ] MatterL2)
    (initial : MatterL2) (time : ℝ) :
    HasDerivAt (fun epsilon => inner ℂ (development.physicalCurve epsilon 0 time initial)
      (current (development.physicalCurve epsilon 0 time initial)))
      (Complex.I*∫ s in (0 : ℝ)..time, kuboKernel perturbation current initial time s) 0 :=
  (development.window (|time|+1) (window_positive time)).current_coupling_kubo
    continuousPerturbation symmetric current initial time (time_inside time)

theorem current_source (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t))
    (preparation : ℝ → MatterFiber →L[ℂ] MatterL2) (continuousPreparation : Continuous preparation)
    (preparedAt : ℝ) (current : MatterL2 →L[ℂ] MatterL2) (time : ℝ) :
    HasDerivAt (fun epsilon => inner ℂ
      (development.physicalCurve epsilon 0 time (normalizedPreparation preparation continuousPreparation preparedAt))
      (current (development.physicalCurve epsilon 0 time (normalizedPreparation preparation continuousPreparation preparedAt))))
      (State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
        (Compatibility.responseMatrix (YangMills.FullPairing.pairedMother 1
          (normalizedPreparationNative preparation continuousPreparation preparedAt
            (responseOperator perturbation continuousPerturbation current time))))) 0 :=
  (development.window (|time|+1) (window_positive time)).current_coupling_source
    continuousPerturbation symmetric preparation continuousPreparation preparedAt current time (time_inside time)

end GlobalPerturbedDevelopment

def globalLocalDevelopment (profile : ℝ → BoundedProfile) (continuousProfile : Continuous profile)
    (realProfile : ∀ t, ∀ᵐ x ∂volume, star (profile t x)=profile t x)
    (data : LorentzianIndex → P286LieBlockData) :
    GlobalPerturbedDevelopment (fun t => localGaugeHamiltonian (profile t) data) :=
  globalPerturbedDevelopment _ (localGaugeHistory_continuous profile continuousProfile data)
    (fun t => localGaugeHamiltonian_selfAdjoint (profile t) (realProfile t) data)

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
