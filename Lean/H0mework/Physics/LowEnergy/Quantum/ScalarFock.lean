import H0mework.Physics.LowEnergy.Quantum.ScalarCCR
import H0mework.Physics.LowEnergy.FullQuantum.CAR
import Mathlib.RingTheory.TensorProduct.Maps

/-! The original scalar Yukawa Hamiltonian on the joint polynomial CCR and
full 252-mode CAR domain. Its independent canonical momentum is not replaced
by a positive-adjoint graph. This is the scalar coupling component. -/
set_option autoImplicit false
namespace SourceScalarFock
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction SU7ExteriorBreakingYukawa SU7ExteriorMatterRestriction
open StageNineDynamicBreakingVacuum QuantizationCheck.Fermion
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineCurrentCoframeMatterTemporalPrincipal Stage9C.Material.SpinPair
open scoped BigOperators TensorProduct Matrix
noncomputable section
attribute [local instance] Fermion.fullIndexOrder

abbrev ScalarIndex := Bool × ScalarBasisIndex

def scalarDirection (a : ScalarIndex) : ExteriorBreakingScalarCarrier :=
  if a.1 then Complex.I • su7ExteriorBasis 4 a.2 else su7ExteriorBasis 4 a.2

theorem scalar_index_card : Fintype.card ScalarIndex = 70 := by
  have basisCard : Fintype.card ScalarBasisIndex = 35 := by
    rw [← Module.finrank_eq_card_basis (su7ExteriorBasis 4)]
    exact exteriorBreakingScalarCarrier_finrank
  simp [ScalarIndex, basisCard]

def scalarCoefficient (φ : ExteriorBreakingScalarCarrier) (a : ScalarIndex) : ℝ :=
  if a.1 then ((su7ExteriorBasis 4).repr φ a.2).im
  else ((su7ExteriorBasis 4).repr φ a.2).re

theorem full_real_scalar_reconstruction (φ : ExteriorBreakingScalarCarrier) :
    ∑ a : ScalarIndex, (scalarCoefficient φ a : ℂ) • scalarDirection a = φ := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  conv_rhs => rw [← (su7ExteriorBasis 4).sum_repr φ]
  apply Finset.sum_congr rfl
  intro a _
  simp only [scalarCoefficient, scalarDirection, Bool.false_eq_true, ↓reduceIte,
    smul_smul, ← add_smul]
  rw [add_comm, Complex.re_add_im]

def sourceMatrix (a : ScalarIndex) : Matrix Quantum.Index Quantum.Index ℂ :=
  Quantum.operatorMatrix (FullQuantum.yukawaHamiltonian (scalarDirection a))

abbrev BosonEnd := SourceScalarCCR.BosonEnd ScalarIndex
abbrev FermionEnd := Module.End ℂ (Fock Quantum.Index)
abbrev JointAlgebra := BosonEnd ⊗[ℂ] FermionEnd
abbrev JointSpace := SourceScalarCCR.BosonSpace ScalarIndex ⊗[ℂ] Fock Quantum.Index

private theorem joint_sum_sub (f g : ScalarIndex → JointAlgebra) :
    (∑ a, f a) - (∑ a, g a) = ∑ a, (f a - g a) :=
  (Finset.sum_sub_distrib f g).symm

def represent : JointAlgebra →ₐ[ℂ] Module.End ℂ JointSpace :=
  Module.endTensorEndAlgHom

def density (a : ScalarIndex) : FermionEnd := Fermion.quantize (sourceMatrix a)

theorem density_original (a : ScalarIndex) (ψ : Fock Quantum.Index) :
    density a ψ = secondQuantize
      (Quantum.operatorMatrix (FullQuantum.yukawaHamiltonian (scalarDirection a))) ψ :=
  Fermion.quantize_apply _ _

def coupling : JointAlgebra :=
  ∑ a : ScalarIndex, SourceScalarCCR.position a ⊗ₜ[ℂ] density a

theorem coupling_tensor_action (f : SourceScalarCCR.BosonSpace ScalarIndex)
    (ψ : Fock Quantum.Index) :
    represent coupling (f ⊗ₜ[ℂ] ψ) =
      ∑ a : ScalarIndex, (MvPolynomial.X a * f) ⊗ₜ[ℂ]
        secondQuantize (sourceMatrix a) ψ := by
  simp only [coupling, map_sum, LinearMap.sum_apply, represent,
    Module.endTensorEndAlgHom_apply, TensorProduct.AlgebraTensorModule.map_tmul,
    SourceScalarCCR.position_apply, density, Fermion.quantize_apply]

set_option backward.isDefEq.respectTransparency false in
theorem coupling_source_oneParticle (u : DiracExteriorMatterCarrier) :
    represent coupling ((1 : SourceScalarCCR.BosonSpace ScalarIndex) ⊗ₜ[ℂ]
      oneParticle (Quantum.coordinates u)) =
      ∑ a : ScalarIndex, MvPolynomial.X a ⊗ₜ[ℂ]
        oneParticle (Quantum.coordinates (FullQuantum.yukawaHamiltonian (scalarDirection a) u)) := by
  rw [coupling_tensor_action]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_one, secondQuantize_oneParticle]
  congr 2
  exact Quantum.matrix_action _ u

def bosonPosition (a : ScalarIndex) : JointAlgebra :=
  SourceScalarCCR.position a ⊗ₜ[ℂ] (1 : FermionEnd)

def bosonMomentum (a : ScalarIndex) : JointAlgebra :=
  SourceScalarCCR.momentum a ⊗ₜ[ℂ] (1 : FermionEnd)

def annihilator (i : Quantum.Index) : JointAlgebra :=
  (1 : BosonEnd) ⊗ₜ[ℂ] Fermion.annihilation i

def momentumCreator (i : Quantum.Index) : JointAlgebra :=
  (1 : BosonEnd) ⊗ₜ[ℂ] Fermion.creation i

private theorem original_primal_zero (p : BasePoint) (k : Fin 3 → ℝ) :
    FullQuantum.primalMatrix actual p k 0 = 1 := by
  have original : FullQuantum.primal actual p k 0 = 1 :=
    LinearMap.ext (FullQuantum.primal_zero actual p k)
  rw [FullQuantum.primalMatrix, original]
  exact Quantum.operatorMatrix.map_one

theorem annihilator_original (p : BasePoint) (k : Fin 3 → ℝ) (i : Quantum.Index) :
    annihilator i = (1 : BosonEnd) ⊗ₜ[ℂ] FullQuantum.annihilator actual p k 0 i := by
  simp [FullQuantum.annihilator, original_primal_zero, Fermion.annihilationField,
    Matrix.one_apply, annihilator]

theorem momentumCreator_original (p : BasePoint) (k : Fin 3 → ℝ) (i : Quantum.Index) :
    momentumCreator i = (1 : BosonEnd) ⊗ₜ[ℂ] FullQuantum.momentumCreator actual p k 0 i := by
  simp [FullQuantum.momentumCreator, original_primal_zero, Fermion.creationField,
    Matrix.one_apply, momentumCreator]

def independentDual (p : BasePoint) (i : Quantum.Index) : JointAlgebra :=
  (1 : BosonEnd) ⊗ₜ[ℂ] FullQuantum.dualCreator actual p 0 0 i

theorem independentDual_original (p : BasePoint) (i : Quantum.Index) :
    independentDual p i =
      (Complex.I / ((|(actual.coframe p).det| : ℝ) : ℂ)) •
        ∑ j : Quantum.Index,
          Quantum.operatorMatrix (currentCoframeMatterTemporalPrincipalInverse
            (actual.coframe p)) j i • momentumCreator j := by
  simp only [independentDual, FullQuantum.dualCreator, neg_zero, original_primal_zero,
    Matrix.one_mul, Fermion.creationField, Matrix.conjTranspose_apply, star_star,
    TensorProduct.tmul_smul, TensorProduct.tmul_sum, momentumCreator]

theorem original_temporal_equation (a : ScalarIndex) (v : DiracExteriorMatterCarrier) :
    (Complex.I * (lapse : ℂ)⁻¹) •
        DiracExteriorMatterAction.diracMatrixMatterAction
          DiracCliffordRepresentation.diracGammaZero
          ((-Complex.I) • FullQuantum.yukawaHamiltonian (scalarDirection a) v) +
      StageNineDiracDualYukawaSpinJurisdiction.diracDualRightChiralYukawaAction
        (scalarDirection a) v = 0 :=
  FullQuantum.yukawa_time_coefficient (scalarDirection a) v

theorem coupling_bosonMomentum (a : ScalarIndex) :
    coupling * bosonMomentum a - bosonMomentum a * coupling =
      Complex.I • ((1 : BosonEnd) ⊗ₜ[ℂ] density a) := by
  classical
  have each (b : ScalarIndex) :
      (SourceScalarCCR.position b * SourceScalarCCR.momentum a) ⊗ₜ[ℂ] density b -
        (SourceScalarCCR.momentum a * SourceScalarCCR.position b) ⊗ₜ[ℂ] density b =
      (if b = a then Complex.I else 0) • ((1 : BosonEnd) ⊗ₜ[ℂ] density b) := by
    by_cases same : b = a
    · simpa only [if_pos same, TensorProduct.sub_tmul, TensorProduct.smul_tmul'] using
        congrArg (fun T : BosonEnd => T ⊗ₜ[ℂ] density b)
          (SourceScalarCCR.position_momentum b a)
    · simpa only [if_neg same, TensorProduct.sub_tmul, TensorProduct.smul_tmul'] using
        congrArg (fun T : BosonEnd => T ⊗ₜ[ℂ] density b)
          (SourceScalarCCR.position_momentum b a)
  simp only [coupling, bosonMomentum, Finset.sum_mul, Finset.mul_sum,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [joint_sum_sub]
  simp_rw [each]
  simp only [ite_smul, zero_smul]
  rw [Finset.sum_eq_single a]
  · exact if_pos rfl
  · intro b _ different
    exact if_neg different
  · intro absent
    exact (absent (Finset.mem_univ a)).elim

theorem boson_momentum_equation (a : ScalarIndex) :
    Complex.I • (coupling * bosonMomentum a - bosonMomentum a * coupling) =
      -((1 : BosonEnd) ⊗ₜ[ℂ] density a) := by
  rw [coupling_bosonMomentum, smul_smul, Complex.I_mul_I]
  exact neg_one_smul ℂ ((1 : BosonEnd) ⊗ₜ[ℂ] density a)

theorem coupling_bosonPosition (a : ScalarIndex) :
    coupling * bosonPosition a = bosonPosition a * coupling := by
  simp only [coupling, bosonPosition, Finset.sum_mul, Finset.mul_sum,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [SourceScalarCCR.position_position]

theorem annihilator_coupling (i : Quantum.Index) :
    annihilator i * coupling - coupling * annihilator i =
      ∑ a : ScalarIndex, SourceScalarCCR.position a ⊗ₜ[ℂ]
        (∑ j : Quantum.Index, sourceMatrix a i j • Fermion.annihilation j) := by
  simp only [annihilator, coupling, Finset.mul_sum, Finset.sum_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [joint_sum_sub]
  simp_rw [← TensorProduct.tmul_sub, density, Fermion.annihilation_quantize]

private theorem creation_car (i j : Quantum.Index) :
    Fermion.creation i * Fermion.creation j +
      Fermion.creation j * Fermion.creation i = 0 := by
  apply LinearMap.ext
  intro ψ
  exact Fermion.create_create_car i j ψ

private theorem creation_word (i j k : Quantum.Index) :
    (Fermion.creation j * Fermion.annihilation k) * Fermion.creation i -
      Fermion.creation i * (Fermion.creation j * Fermion.annihilation k) =
      if k = i then Fermion.creation j else 0 := by
  calc
    _ = Fermion.creation j *
        (Fermion.annihilation k * Fermion.creation i +
          Fermion.creation i * Fermion.annihilation k) -
        (Fermion.creation j * Fermion.creation i +
          Fermion.creation i * Fermion.creation j) * Fermion.annihilation k := by
      noncomm_ring
    _ = _ := by rw [Fermion.operator_car, creation_car]; split <;> simp_all

theorem quantize_momentumCreator (H : Matrix Quantum.Index Quantum.Index ℂ)
    (i : Quantum.Index) :
    Fermion.quantize H * Fermion.creation i - Fermion.creation i * Fermion.quantize H =
      ∑ j : Quantum.Index, H j i • Fermion.creation j := by
  simp only [Fermion.quantize, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  have weighted (c : ℂ) (A B : FermionEnd) : c • A - c • B = c • (A - B) :=
    (smul_sub c A B).symm
  simp_rw [weighted, creation_word]
  simp [smul_ite]

theorem coupling_momentumCreator (i : Quantum.Index) :
    coupling * momentumCreator i - momentumCreator i * coupling =
      ∑ a : ScalarIndex, SourceScalarCCR.position a ⊗ₜ[ℂ]
        (∑ j : Quantum.Index, sourceMatrix a j i • Fermion.creation j) := by
  simp only [momentumCreator, coupling, Finset.mul_sum, Finset.sum_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [joint_sum_sub]
  simp_rw [← TensorProduct.tmul_sub, density, quantize_momentumCreator]

theorem canonical_CAR (i j : Quantum.Index) :
    annihilator i * momentumCreator j + momentumCreator j * annihilator i =
      (if i = j then 1 else 0 : ℂ) • (1 : JointAlgebra) := by
  simp only [annihilator, momentumCreator, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← TensorProduct.tmul_add, Fermion.operator_car]
  split <;> simp_all [Algebra.TensorProduct.one_def]

theorem source_matrix_product_zero (a b : ScalarIndex) :
    sourceMatrix a * sourceMatrix b = 0 := by
  have h : (FullQuantum.yukawaHamiltonian (scalarDirection a)).comp
      (FullQuantum.yukawaHamiltonian (scalarDirection b)) = 0 := by
    simpa only [Module.End.one_eq_id, LinearMap.id_comp] using FullQuantum.yukawa_time_insertions
      (scalarDirection a) (scalarDirection b) (1 : FullQuantum.Mother) (by rfl)
  rw [sourceMatrix, sourceMatrix, ← Quantum.matrix_composition, h]
  exact Quantum.operatorMatrix.map_zero

theorem density_normal_order (a b : ScalarIndex) :
    density a * density b = Fermion.normalProduct (sourceMatrix a) (sourceMatrix b) := by
  rw [density, density, Fermion.quantize_normal_order, source_matrix_product_zero]
  simp [Fermion.quantize]

theorem density_twoParticle (a b : ScalarIndex) (u v : DiracExteriorMatterCarrier) :
    (density a * density b) (Fermion.sourcePair u v) =
      Fermion.sourcePair (FullQuantum.yukawaHamiltonian (scalarDirection a) u)
        (FullQuantum.yukawaHamiltonian (scalarDirection b) v) -
      Fermion.sourcePair (FullQuantum.yukawaHamiltonian (scalarDirection a) v)
        (FullQuantum.yukawaHamiltonian (scalarDirection b) u) := by
  rw [density_normal_order]
  simp only [Fermion.sourcePair, Fermion.normalProduct_twoParticle, sourceMatrix,
    ← Quantum.matrix_action]

theorem coupling_square_normal_order :
    coupling * coupling = ∑ a : ScalarIndex, ∑ b : ScalarIndex,
      (SourceScalarCCR.position a * SourceScalarCCR.position b) ⊗ₜ[ℂ]
        Fermion.normalProduct (sourceMatrix a) (sourceMatrix b) := by
  simp only [coupling, Finset.sum_mul, Finset.mul_sum,
    Algebra.TensorProduct.tmul_mul_tmul, density_normal_order]
  rw [Finset.sum_comm]

end
end SourceScalarFock
