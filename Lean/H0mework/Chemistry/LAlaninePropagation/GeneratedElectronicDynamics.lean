import H0mework.Chemistry.LAlaninePropagation.NativeElectronicPropagation
import H0mework.Quantum.Generator.P257

/-!
# Finite source-generated electronic dynamics

Source upper triangles generate self-adjoint operators. P257 supplies their
unitary Schrödinger flow. The conjugated density has its actual commutator
derivative; no exact-projector or thermodynamic interpretation is imposed on
the quantized initial density.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Propagation.Dynamics

open Interface
open _root_.SaturationMonoid.AffineRelaxation

noncomputable section

abbrev ElectronicSpace := EuclideanSpace ℂ Basis
abbrev ElectronicOperator := ElectronicSpace →L[ℂ] ElectronicSpace

theorem activeNumerator_swap (source : ElectronicPropagationSource) (i j : Basis) :
    activeNumerator source i j = activeNumerator source j i := by
  simp only [activeNumerator, symmetricEntry_swap _ i j]

theorem activeMatrix_hermitian (source : ElectronicPropagationSource) :
    (activeMatrix source).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star ((activeNumerator source j i : ℂ) / 1000000000000000) = _
  rw [activeNumerator_swap source j i]
  simp [activeMatrix]

theorem initialDensityMatrix_hermitian (source : ElectronicPropagationSource) :
    (initialDensityMatrix source).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star ((symmetricEntry source.d0Q j i : ℂ) / 1000000000000) = _
  rw [symmetricEntry_swap source.d0Q j i]
  simp [initialDensityMatrix]

def matrixOperatorEquiv : Matrix Basis Basis ℂ ≃⋆ₐ[ℂ] ElectronicOperator :=
  Matrix.toEuclideanCLM (n := Basis) (𝕜 := ℂ)

def hamiltonian (source : ElectronicPropagationSource) : ElectronicOperator :=
  matrixOperatorEquiv (activeMatrix source)

def initialDensity (source : ElectronicPropagationSource) : ElectronicOperator :=
  matrixOperatorEquiv (initialDensityMatrix source)

theorem hamiltonian_selfAdjoint (source : ElectronicPropagationSource) :
    IsSelfAdjoint (hamiltonian source) :=
  (activeMatrix_hermitian source).isSelfAdjoint.map matrixOperatorEquiv

theorem initialDensity_selfAdjoint (source : ElectronicPropagationSource) :
    IsSelfAdjoint (initialDensity source) :=
  (initialDensityMatrix_hermitian source).isSelfAdjoint.map matrixOperatorEquiv

/-- The existing bounded Hamiltonian producer is consumed without a supplied flow. -/
theorem schrodingerFlow (source : ElectronicPropagationSource) :
    BoundedSelfAdjointHamiltonianSchrodingerFlowCertificate
      ElectronicSpace (hamiltonian source) :=
  boundedSelfAdjointHamiltonianSchrodingerFlowCertificate
    (hamiltonian source) (hamiltonian_selfAdjoint source)

def propagator (source : ElectronicPropagationSource) (time : ℝ) : ElectronicOperator :=
  NormedSpace.exp ((time : ℂ) • (-Complex.I • hamiltonian source))

theorem propagator_eq_realExp (source : ElectronicPropagationSource) (time : ℝ) :
    propagator source time =
      NormedSpace.exp (time • (-(Complex.I • hamiltonian source))) := by
  unfold propagator
  congr 1
  ext state i
  simp [Complex.real_smul]

@[simp] theorem propagator_zero (source : ElectronicPropagationSource) :
    propagator source 0 = 1 :=
  (schrodingerFlow source).exponential_group.zero_slice

theorem propagator_unitary (source : ElectronicPropagationSource) (time : ℝ) :
    propagator source time ∈ unitary ElectronicOperator :=
  (schrodingerFlow source).exponential_group.unitarySlice time

theorem propagator_add (source : ElectronicPropagationSource) (time next : ℝ) :
    propagator source (time + next) = propagator source time * propagator source next :=
  (schrodingerFlow source).exponential_group.addSlice time next

theorem propagator_mul_neg (source : ElectronicPropagationSource) (time : ℝ) :
    propagator source time * propagator source (-time) = 1 := by
  rw [← propagator_add, add_neg_cancel, propagator_zero]

theorem propagator_neg_mul (source : ElectronicPropagationSource) (time : ℝ) :
    propagator source (-time) * propagator source time = 1 := by
  rw [← propagator_add, neg_add_cancel, propagator_zero]

theorem propagator_neg_eq_star (source : ElectronicPropagationSource) (time : ℝ) :
    propagator source (-time) = star (propagator source time) :=
  left_inv_eq_right_inv (propagator_neg_mul source time)
    (Unitary.mul_star_self_of_mem (propagator_unitary source time))

theorem propagator_preserves_norm (source : ElectronicPropagationSource)
    (time : ℝ) (state : ElectronicSpace) :
    ‖propagator source time state‖ = ‖state‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (propagator_unitary source time) state

theorem propagator_hasDerivAt (source : ElectronicPropagationSource) (time : ℝ) :
    HasDerivAt (propagator source)
      ((-(Complex.I • hamiltonian source)) * propagator source time) time := by
  change HasDerivAt (fun t : ℝ => propagator source t) _ time
  simpa only [propagator_eq_realExp] using!
    (schrodingerFlow source).schrodinger_equation.operator_derivative time

theorem propagatedState_hasDerivAt (source : ElectronicPropagationSource)
    (time : ℝ) (state : ElectronicSpace) :
    HasDerivAt (fun t => propagator source t state)
      ((-(Complex.I • hamiltonian source)) (propagator source time state)) time := by
  simpa only [propagator_eq_realExp] using!
    (schrodingerFlow source).orbitDerivative time state

def densityEvolution (source : ElectronicPropagationSource) (time : ℝ) : ElectronicOperator :=
  propagator source time * initialDensity source * propagator source (-time)

@[simp] theorem densityEvolution_zero (source : ElectronicPropagationSource) :
    densityEvolution source 0 = initialDensity source := by
  simp [densityEvolution]

def densityTangent (source : ElectronicPropagationSource) : ElectronicOperator :=
  -(Complex.I •
    (hamiltonian source * initialDensity source - initialDensity source * hamiltonian source))

theorem densityEvolution_hasDerivAt_zero (source : ElectronicPropagationSource) :
    HasDerivAt (densityEvolution source) (densityTangent source) 0 := by
  have forward : HasDerivAt (propagator source) (-(Complex.I • hamiltonian source)) 0 := by
    simpa only [propagator_zero, mul_one] using propagator_hasDerivAt source 0
  have backward : HasDerivAt (fun t : ℝ => propagator source (-t))
      (Complex.I • hamiltonian source) 0 := by
    have atNeg : HasDerivAt (propagator source)
        (-(Complex.I • hamiltonian source)) (-(0 : ℝ)) := by
      simpa using forward
    simpa using! atNeg.scomp 0 ((hasDerivAt_id (0 : ℝ)).neg)
  have derivative := (forward.mul_const (initialDensity source)).mul backward
  change HasDerivAt (densityEvolution source) _ 0 at derivative
  apply derivative.congr_deriv
  simp only [neg_zero, propagator_zero, mul_one, one_mul, densityTangent]
  ext state
  simp
  ring

def integerCommutator (source : ElectronicPropagationSource) (i j : Basis) : Int :=
  ∑ k : Basis,
    (activeNumerator source i k * symmetricEntry source.d0Q k j -
      symmetricEntry source.d0Q i k * activeNumerator source k j)

theorem commutator_entry_eq_scaled (source : ElectronicPropagationSource) (i j : Basis) :
    (activeMatrix source * initialDensityMatrix source -
      initialDensityMatrix source * activeMatrix source) i j =
        (integerCommutator source i j : ℂ) / 1000000000000000000000000000 := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, activeMatrix, initialDensityMatrix,
    integerCommutator, Int.cast_sum, Int.cast_sub, Int.cast_mul]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _membership
  ring

theorem operatorCommutator_ne_of_integer (source : ElectronicPropagationSource)
    (i j : Basis) (nonzero : integerCommutator source i j ≠ 0) :
    hamiltonian source * initialDensity source - initialDensity source * hamiltonian source ≠ 0 := by
  intro zero
  have matrixZero : activeMatrix source * initialDensityMatrix source -
      initialDensityMatrix source * activeMatrix source = 0 := by
    apply matrixOperatorEquiv.injective
    change matrixOperatorEquiv
      (activeMatrix source * initialDensityMatrix source -
        initialDensityMatrix source * activeMatrix source) = matrixOperatorEquiv 0
    rw [map_sub, map_mul, map_mul, map_zero]
    exact zero
  have entryZero := congrArg (fun matrix : Matrix Basis Basis ℂ => matrix i j) matrixZero
  rw [commutator_entry_eq_scaled] at entryZero
  have integerNonzero : (integerCommutator source i j : ℂ) ≠ 0 := by
    exact_mod_cast nonzero
  exact (div_ne_zero integerNonzero (by norm_num)) entryZero

/-- A source-derived nonzero commutator rules out a frozen density trajectory. -/
theorem densityEvolution_not_constant (source : ElectronicPropagationSource)
    (i j : Basis) (nonzero : integerCommutator source i j ≠ 0) :
    ¬ ∀ time : ℝ, densityEvolution source time = initialDensity source := by
  intro constant
  have functionEqual : densityEvolution source = fun _ : ℝ => initialDensity source :=
    funext constant
  have derivative := densityEvolution_hasDerivAt_zero source
  rw [functionEqual] at derivative
  have tangentZero := derivative.unique (hasDerivAt_const (0 : ℝ) (initialDensity source))
  have smulZero : Complex.I • (hamiltonian source * initialDensity source -
      initialDensity source * hamiltonian source) = 0 :=
    neg_eq_zero.mp tangentZero
  exact operatorCommutator_ne_of_integer source i j nonzero
    ((smul_eq_zero.mp smulZero).resolve_left Complex.I_ne_zero)

end

end LAlanine40K2025.Propagation.Dynamics
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
