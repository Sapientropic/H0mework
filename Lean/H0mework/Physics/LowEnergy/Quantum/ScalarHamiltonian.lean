import H0mework.Physics.LowEnergy.Quantum.ScalarHamiltonianBoson
import H0mework.Physics.LowEnergy.Quantum.RealScalarFock

/-! One joint polynomial/real-CAR Hamiltonian consumes a finite scalar frame,
its independent momentum frame, a symmetric real phase Hessian and the
original full matter generator. Concrete source frame/Hessian data remain
explicit inputs, including the Fourier-pair ordering. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SourceScalarHamiltonian
open SourceScalarCCR
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction QuantizationCheck.Fermion
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineDynamicBreakingVacuum
open scoped BigOperators TensorProduct Matrix
noncomputable section
attribute [local instance] Fermion.fullIndexOrder SourceRealScalarFock.branchOrder

abbrev ScalarIndex := SourceScalarFock.ScalarIndex
abbrev BranchIndex := SourceRealScalarFock.BranchIndex
abbrev FermionEnd := Module.End ℂ (Fock BranchIndex)
abbrev JointAlgebra (σ : Type*) := BosonEnd σ ⊗[ℂ] FermionEnd
abbrev JointSpace (σ : Type*) := BosonSpace σ ⊗[ℂ] Fock BranchIndex

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def quantizeLinear : Matrix BranchIndex BranchIndex ℂ →ₗ[ℂ] FermionEnd where
  toFun := Fermion.quantize
  map_add' A B := by simp [Fermion.quantize, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by simp [Fermion.quantize, Finset.smul_sum, smul_smul]

def projectedMatrix (R : ScalarIndex → σ → ℝ) (a : σ) : Matrix BranchIndex BranchIndex ℂ :=
  ∑ A : ScalarIndex, (R A a : ℂ) • SourceRealScalarFock.sourceMatrix A

def projectedDensity (R : ScalarIndex → σ → ℝ) (a : σ) : FermionEnd :=
  quantizeLinear (projectedMatrix R a)

omit [Fintype σ] [DecidableEq σ] in
theorem projected_density_original (R : ScalarIndex → σ → ℝ) (a : σ) :
    projectedDensity R a =
      ∑ A : ScalarIndex, (R A a : ℂ) • SourceRealScalarFock.rawRealCurrent A := by
  simp only [projectedDensity, projectedMatrix, map_sum, map_smul,
    SourceRealScalarFock.original_half_normalization]
  rfl

def fieldPosition (R : ScalarIndex → σ → ℝ) (A : ScalarIndex) : BosonEnd σ :=
  ∑ a : σ, (R A a : ℂ) • position a

def fieldMomentum (D : ScalarIndex → σ → ℝ) (A : ScalarIndex) : BosonEnd σ :=
  ∑ a : σ, (D A a : ℂ) • momentum a

theorem frame_CCR (R D : ScalarIndex → σ → ℝ) (A B : ScalarIndex) :
    fieldPosition R A * fieldMomentum D B - fieldMomentum D B * fieldPosition R A =
      (Complex.I * (∑ a : σ, R A a * D B a : ℝ)) • (1 : BosonEnd σ) := by
  simp only [fieldPosition, fieldMomentum, Finset.sum_mul, Finset.mul_sum,
    smul_mul_smul]
  rw [Finset.sum_comm (f := fun b a : σ =>
    ((R A a : ℂ) * (D B b : ℂ)) • (position a * momentum b))]
  simp_rw [mul_comm (D B _ : ℂ)]
  rw [← Finset.sum_sub_distrib]
  have weighted (c : ℂ) (X Y : BosonEnd σ) : c • X - c • Y = c • (X - Y) :=
    (smul_sub c X Y).symm
  simp_rw [← Finset.sum_sub_distrib, weighted, position_momentum]
  simp [smul_ite, smul_smul, Complex.ofReal_sum, Finset.sum_smul, Finset.mul_sum,
    mul_comm]

def interaction (R : ScalarIndex → σ → ℝ) : JointAlgebra σ :=
  ∑ a : σ, position a ⊗ₜ[ℂ] projectedDensity R a

omit [DecidableEq σ] in
theorem interaction_original_field (R : ScalarIndex → σ → ℝ) :
    interaction R = ∑ A : ScalarIndex,
      fieldPosition R A ⊗ₜ[ℂ] SourceRealScalarFock.rawRealCurrent A := by
  simp only [interaction, projected_density_original, TensorProduct.tmul_sum,
    TensorProduct.tmul_smul, fieldPosition, TensorProduct.sum_tmul,
    TensorProduct.smul_tmul']
  rw [Finset.sum_comm]

def fullMatterMatrix (point : BasePoint) (k : Fin 3 → ℝ) : Matrix BranchIndex BranchIndex ℂ :=
  Matrix.fromBlocks (Quantum.operatorMatrix (FullQuantum.hamiltonian actual point k))
    0 0 (-((Quantum.operatorMatrix (FullQuantum.hamiltonian actual point (-k))).map star))

theorem full_matter_plus (point : BasePoint) (k : Fin 3 → ℝ) :
    (fullMatterMatrix point k).submatrix Sum.inl Sum.inl =
      Quantum.operatorMatrix (FullQuantum.hamiltonian actual point k) := rfl

theorem full_matter_conjugate (point : BasePoint) (k : Fin 3 → ℝ) :
    (fullMatterMatrix point k).submatrix Sum.inr Sum.inr =
      -((Quantum.operatorMatrix (FullQuantum.hamiltonian actual point (-k))).map star) := rfl

def hamiltonian (R : ScalarIndex → σ → ℝ) (K : Matrix (σ ⊕ σ) (σ ⊕ σ) ℝ)
    (point : BasePoint) (k : Fin 3 → ℝ) : JointAlgebra σ :=
  quadratic K ⊗ₜ[ℂ] (1 : FermionEnd) +
    (1 : BosonEnd σ) ⊗ₜ[ℂ] quantizeLinear (fullMatterMatrix point k) + interaction R

def represent : JointAlgebra σ →ₐ[ℂ] Module.End ℂ (JointSpace σ) :=
  Module.endTensorEndAlgHom

def evolve (X : JointAlgebra σ) : JointAlgebra σ →ₗ[ℂ] JointAlgebra σ where
  toFun H := Complex.I • (H * X - X * H)
  map_add' H K := by
    simp only [add_mul, mul_add]
    module
  map_smul' c H := by
    change Complex.I • ((c • H) * X - X * (c • H)) =
      c • (Complex.I • (H * X - X * H))
    rw [smul_mul_assoc, mul_smul_comm]
    have weighted : c • (H * X) - c • (X * H) = c • (H * X - X * H) :=
      (smul_sub c (H * X) (X * H)).symm
    rw [weighted, smul_smul, smul_smul, mul_comm Complex.I c]

omit [Fintype σ] [DecidableEq σ] in
theorem evolve_apply (X H : JointAlgebra σ) :
    evolve X H = Complex.I • (H * X - X * H) := rfl

omit [Fintype σ] [DecidableEq σ] in
theorem evolve_boson_tensor (X H : BosonEnd σ) (T : FermionEnd) :
    evolve (X ⊗ₜ[ℂ] (1 : FermionEnd)) (H ⊗ₜ[ℂ] T) = read X H ⊗ₜ[ℂ] T := by
  simp only [evolve_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
    ← TensorProduct.sub_tmul, read_apply, TensorProduct.smul_tmul']

omit [Fintype σ] [DecidableEq σ] in
theorem read_one (X : BosonEnd σ) : read X 1 = 0 := by
  simp only [read_apply, one_mul, mul_one, sub_self, smul_zero]

omit [DecidableEq σ] in
theorem interaction_position (R : ScalarIndex → σ → ℝ) (a : σ) :
    evolve (position a ⊗ₜ[ℂ] (1 : FermionEnd)) (interaction R) = 0 := by
  simp only [interaction, map_sum, evolve_boson_tensor, position_position_read,
    TensorProduct.zero_tmul, Finset.sum_const_zero]

theorem interaction_momentum (R : ScalarIndex → σ → ℝ) (a : σ) :
    evolve (momentum a ⊗ₜ[ℂ] (1 : FermionEnd)) (interaction R) =
      -((1 : BosonEnd σ) ⊗ₜ[ℂ] projectedDensity R a) := by
  have each (b : σ) :
      evolve (momentum a ⊗ₜ[ℂ] (1 : FermionEnd)) (position b ⊗ₜ[ℂ] projectedDensity R b) =
        if b = a then -((1 : BosonEnd σ) ⊗ₜ[ℂ] projectedDensity R b) else 0 := by
    rw [evolve_boson_tensor, momentum_position_read]
    by_cases same : b = a
    · rw [if_pos same, if_pos same]
      have negative : (-1 : ℂ) • (1 : BosonEnd σ) = -(1 : BosonEnd σ) :=
        neg_one_smul ℂ (1 : BosonEnd σ)
      rw [negative]
      exact TensorProduct.neg_tmul (1 : BosonEnd σ) (projectedDensity R b)
    · rw [if_neg same, if_neg same, zero_smul, TensorProduct.zero_tmul]
  simp only [interaction, map_sum, each]
  rw [Finset.sum_eq_single a]
  · exact if_pos rfl
  · intro b _ different; exact if_neg different
  · intro absent; exact (absent (Finset.mem_univ a)).elim

theorem position_equation (R : ScalarIndex → σ → ℝ)
    (K : Matrix (σ ⊕ σ) (σ ⊕ σ) ℝ) (symmetric : ∀ i j, K i j = K j i)
    (point : BasePoint) (k : Fin 3 → ℝ) (a : σ) :
    evolve (position a ⊗ₜ[ℂ] (1 : FermionEnd)) (hamiltonian R K point k) =
      (∑ j : σ ⊕ σ, (K (Sum.inr a) j : ℂ) • phase j) ⊗ₜ[ℂ] (1 : FermionEnd) := by
  simp only [hamiltonian, map_add, evolve_boson_tensor, read_one,
    TensorProduct.zero_tmul, add_zero, interaction_position, quadratic_position K symmetric]

theorem momentum_equation (R : ScalarIndex → σ → ℝ)
    (K : Matrix (σ ⊕ σ) (σ ⊕ σ) ℝ) (symmetric : ∀ i j, K i j = K j i)
    (point : BasePoint) (k : Fin 3 → ℝ) (a : σ) :
    evolve (momentum a ⊗ₜ[ℂ] (1 : FermionEnd)) (hamiltonian R K point k) =
      -((∑ j : σ ⊕ σ, (K (Sum.inl a) j : ℂ) • phase j) ⊗ₜ[ℂ] (1 : FermionEnd)) -
        (1 : BosonEnd σ) ⊗ₜ[ℂ] projectedDensity R a := by
  simp only [hamiltonian, map_add, evolve_boson_tensor, read_one,
    TensorProduct.zero_tmul, add_zero, interaction_momentum, quadratic_momentum K symmetric,
    sub_eq_add_neg, TensorProduct.neg_tmul]

def fermionStep (X H : FermionEnd) : FermionEnd := Complex.I • (H * X - X * H)

omit [Fintype σ] [DecidableEq σ] in
theorem evolve_fermion_tensor (X T : FermionEnd) (H : BosonEnd σ) :
    evolve ((1 : BosonEnd σ) ⊗ₜ[ℂ] X) (H ⊗ₜ[ℂ] T) = H ⊗ₜ[ℂ] fermionStep X T := by
  simp only [evolve_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
    ← TensorProduct.tmul_sub, fermionStep, TensorProduct.tmul_smul]

theorem fermionStep_one (X : FermionEnd) : fermionStep X 1 = 0 := by
  simp only [fermionStep, one_mul, mul_one, sub_self, smul_zero]

theorem annihilation_step (W : Matrix BranchIndex BranchIndex ℂ) (i : BranchIndex) :
    fermionStep (Fermion.annihilation i) (quantizeLinear W) =
      (-Complex.I) • Fermion.annihilationField W i := by
  have reverse : quantizeLinear W * Fermion.annihilation i -
      Fermion.annihilation i * quantizeLinear W =
      -(Fermion.annihilation i * quantizeLinear W - quantizeLinear W * Fermion.annihilation i) := by abel
  rw [fermionStep, reverse]
  change Complex.I • -(Fermion.annihilation i * Fermion.quantize W -
    Fermion.quantize W * Fermion.annihilation i) = _
  rw [Fermion.annihilation_quantize]
  exact (smul_neg Complex.I (Fermion.annihilationField W i)).trans
    (neg_smul Complex.I (Fermion.annihilationField W i)).symm

def momentumColumn (W : Matrix BranchIndex BranchIndex ℂ) (i : BranchIndex) : FermionEnd :=
  ∑ j : BranchIndex, W j i • Fermion.creation j

private theorem creator_car (i j : BranchIndex) :
    Fermion.creation i * Fermion.creation j + Fermion.creation j * Fermion.creation i = 0 := by
  apply LinearMap.ext
  intro ψ
  exact Fermion.create_create_car i j ψ

private theorem creator_word (i j k : BranchIndex) :
    (Fermion.creation j * Fermion.annihilation k) * Fermion.creation i -
      Fermion.creation i * (Fermion.creation j * Fermion.annihilation k) =
      if k = i then Fermion.creation j else 0 := by
  calc
    _ = Fermion.creation j * (Fermion.annihilation k * Fermion.creation i +
        Fermion.creation i * Fermion.annihilation k) -
        (Fermion.creation j * Fermion.creation i + Fermion.creation i * Fermion.creation j) *
          Fermion.annihilation k := by noncomm_ring
    _ = _ := by rw [Fermion.operator_car, creator_car]; split <;> simp_all

theorem creator_step (W : Matrix BranchIndex BranchIndex ℂ) (i : BranchIndex) :
    fermionStep (Fermion.creation i) (quantizeLinear W) = Complex.I • momentumColumn W i := by
  have equation : Fermion.quantize W * Fermion.creation i -
      Fermion.creation i * Fermion.quantize W = momentumColumn W i := by
    simp only [Fermion.quantize, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    have weighted (c : ℂ) (X Y : FermionEnd) : c • X - c • Y = c • (X - Y) :=
      (smul_sub c X Y).symm
    simp_rw [weighted, creator_word]
    simp [smul_ite, momentumColumn]
  exact congrArg (fun X : FermionEnd => Complex.I • X) equation

omit [DecidableEq σ] in
theorem primal_equation (R : ScalarIndex → σ → ℝ)
    (K : Matrix (σ ⊕ σ) (σ ⊕ σ) ℝ) (point : BasePoint) (k : Fin 3 → ℝ) (i : BranchIndex) :
    evolve ((1 : BosonEnd σ) ⊗ₜ[ℂ] Fermion.annihilation i) (hamiltonian R K point k) =
      (1 : BosonEnd σ) ⊗ₜ[ℂ]
        ((-Complex.I) • Fermion.annihilationField (fullMatterMatrix point k) i) +
      ∑ a : σ, position a ⊗ₜ[ℂ]
        ((-Complex.I) • Fermion.annihilationField (projectedMatrix R a) i) := by
  simp only [hamiltonian, map_add, interaction, map_sum, evolve_fermion_tensor,
    fermionStep_one, TensorProduct.tmul_zero, zero_add, projectedDensity, annihilation_step]

omit [DecidableEq σ] in
theorem independent_momentum_equation (R : ScalarIndex → σ → ℝ)
    (K : Matrix (σ ⊕ σ) (σ ⊕ σ) ℝ) (point : BasePoint) (k : Fin 3 → ℝ) (i : BranchIndex) :
    evolve ((1 : BosonEnd σ) ⊗ₜ[ℂ] Fermion.creation i) (hamiltonian R K point k) =
      (1 : BosonEnd σ) ⊗ₜ[ℂ] (Complex.I • momentumColumn (fullMatterMatrix point k) i) +
      ∑ a : σ, position a ⊗ₜ[ℂ] (Complex.I • momentumColumn (projectedMatrix R a) i) := by
  simp only [hamiltonian, map_add, interaction, map_sum, evolve_fermion_tensor,
    fermionStep_one, TensorProduct.tmul_zero, zero_add, projectedDensity, creator_step]

def matrixBilinear (p ψ : BranchIndex → ℂ) : Matrix BranchIndex BranchIndex ℂ →ₗ[ℂ] ℂ where
  toFun W := ∑ i, ∑ j, p i * W i j * ψ j
  map_add' W V := by simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c W := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

omit [Fintype σ] [DecidableEq σ] in
theorem projected_original_real_source (R : ScalarIndex → σ → ℝ) (a : σ)
    (point : BasePoint) (χ : Module.Dual ℂ DiracExteriorMatterCarrier)
    (ψ : DiracExteriorMatterCarrier) :
    matrixBilinear
      (SourceRealScalarFock.normalizedMomentum
        (Quantum.dualCoordinates (FullQuantum.normalizedMomentum actual point χ)))
      (SourceRealScalarFock.normalizedPrimal (Quantum.coordinates ψ)) (projectedMatrix R a) =
      -∑ A : ScalarIndex, (R A a : ℂ) *
        (Exchange.yukawaSource (actual.coframe point) ψ χ
          (scalarCoordinateEquiv (SourceScalarFock.scalarDirection A)) : ℂ) := by
  rw [projectedMatrix, map_sum]
  simp only [map_smul, smul_eq_mul]
  have source (A : ScalarIndex) :
      matrixBilinear
        (SourceRealScalarFock.normalizedMomentum
          (Quantum.dualCoordinates (FullQuantum.normalizedMomentum actual point χ)))
        (SourceRealScalarFock.normalizedPrimal (Quantum.coordinates ψ))
        (SourceRealScalarFock.sourceMatrix A) =
      -(Exchange.yukawaSource (actual.coframe point) ψ χ
        (scalarCoordinateEquiv (SourceScalarFock.scalarDirection A)) : ℂ) :=
    SourceRealScalarFock.original_real_action_branches A point χ ψ
  simp only [source, mul_neg, Finset.sum_neg_distrib]

omit [DecidableEq σ] in
theorem represented_hamiltonian_action (R : ScalarIndex → σ → ℝ)
    (K : Matrix (σ ⊕ σ) (σ ⊕ σ) ℝ) (point : BasePoint) (k : Fin 3 → ℝ)
    (f : BosonSpace σ) (ψ : Fock BranchIndex) :
    represent (hamiltonian R K point k) (f ⊗ₜ[ℂ] ψ) =
      quadratic K f ⊗ₜ[ℂ] ψ +
      f ⊗ₜ[ℂ] quantizeLinear (fullMatterMatrix point k) ψ +
      ∑ a : σ, (MvPolynomial.X a * f) ⊗ₜ[ℂ] projectedDensity R a ψ := by
  simp only [hamiltonian, interaction, map_add, map_sum, represent,
    LinearMap.add_apply, LinearMap.sum_apply, Module.endTensorEndAlgHom_apply,
    TensorProduct.AlgebraTensorModule.map_tmul, Module.End.one_apply, position_apply]

omit [Fintype σ] [DecidableEq σ] in
theorem represented_heisenberg (X H : JointAlgebra σ) (state : JointSpace σ) :
    represent (evolve X H) state =
      Complex.I • (represent H (represent X state) - represent X (represent H state)) := by
  simp only [evolve_apply, map_smul, map_sub, map_mul, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.mul_apply]

omit [Fintype σ] [DecidableEq σ] in
private theorem evolve_swap (X H : JointAlgebra σ) : evolve X H = -evolve H X := by
  simp only [evolve_apply]
  module


end
end SourceScalarHamiltonian
