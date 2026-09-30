import H0mework.Physics.LowEnergy.FullQuantum.GaugeGreen.Coercivity

/-! The original full free resolvent has a continuous uniformly controlled spatial multiplier. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
open FullSpace Retarded YangMills.FullPairing ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Triangular
noncomputable section

private theorem operator_one : operator (1 : Mother)=(1 : FiberOperators) := by ext v; simp [operator]
private theorem operator_sub (A B : Mother) : operator (A-B)=operator A-operator B := by ext v; simp [operator]

def freeKernelOperator (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping : ℝ) : FiberOperators :=
  operator (freeKernel actual point momentum (spectralParameter energy damping))

theorem freeValue_two_sided (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    freeKernelOperator point momentum energy damping*freeValue point momentum energy damping=1 ∧
      freeValue point momentum energy damping*freeKernelOperator point momentum energy damping=1 := by
  constructor
  · rw [freeKernelOperator,freeValue,freeResolvent,← operator_mul,
      Ring.mul_inverse_cancel _ (sourceFree_regular point momentum energy damping positive),operator_one]
  · rw [freeKernelOperator,freeValue,freeResolvent,← operator_mul,
      Ring.inverse_mul_cancel _ (sourceFree_regular point momentum energy damping positive),operator_one]

def freeUnit (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) : FiberOperatorsˣ :=
  ⟨freeKernelOperator point momentum energy damping,freeValue point momentum energy damping,
    (freeValue_two_sided point momentum energy damping positive).1,
    (freeValue_two_sided point momentum energy damping positive).2⟩

theorem freeValue_eq_inverse (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    freeValue point momentum energy damping=Ring.inverse (freeKernelOperator point momentum energy damping) :=
  (Ring.inverse_unit (freeUnit point momentum energy damping positive)).symm

theorem freeKernelOperator_continuous (point : BasePoint) (energy damping : ℝ) :
    Continuous (fun momentum : Fin 3 → ℝ => freeKernelOperator point momentum energy damping) := by
  simp only [freeKernelOperator,freeKernel,operator_sub,operator_smul,operator_one]
  exact continuous_const.sub (original_freeHamiltonian_continuous point)

theorem freeValue_continuous (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) :
    Continuous (fun momentum : Fin 3 → ℝ => freeValue point momentum energy damping) := by
  apply continuous_iff_continuousAt.mpr
  intro momentum
  have inverse := NormedRing.inverse_continuousAt (freeUnit point momentum energy damping positive)
  have atKernel : ContinuousAt (Ring.inverse : FiberOperators → FiberOperators)
      (freeKernelOperator point momentum energy damping) := inverse
  have composite := atKernel.comp (f := fun k : Fin 3 → ℝ => freeKernelOperator point k energy damping)
    (x := momentum) (freeKernelOperator_continuous point energy damping).continuousAt
  simpa only [Function.comp_def,← freeValue_eq_inverse point _ energy damping positive] using composite

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
