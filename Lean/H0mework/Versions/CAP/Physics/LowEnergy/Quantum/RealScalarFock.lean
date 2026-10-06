import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.ScalarFock

/-! The complexification of the original real independent-dual action.
The two branches describe the original real coordinates; no positive adjoint
condition or additional physical particle interpretation is imposed. -/
set_option autoImplicit false
namespace SourceRealScalarFock
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction QuantizationCheck.Fermion
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineCurrentCoframeMatterTemporalPrincipal Stage9C.Material.SpinPair
open StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction
open scoped BigOperators TensorProduct Matrix
noncomputable section
attribute [local instance] Fermion.fullIndexOrder

abbrev ScalarIndex := SourceScalarFock.ScalarIndex
abbrev BranchIndex := Quantum.Index ⊕ Quantum.Index
abbrev branchOrder : LinearOrder BranchIndex :=
  LinearOrder.lift' (Fintype.equivFin BranchIndex) (Fintype.equivFin BranchIndex).injective
attribute [local instance] branchOrder

def branches (W : Matrix Quantum.Index Quantum.Index ℂ) : Matrix BranchIndex BranchIndex ℂ :=
  Matrix.fromBlocks W 0 0 (-(W.map star))

def sourceMatrix (a : ScalarIndex) : Matrix BranchIndex BranchIndex ℂ :=
  branches (SourceScalarFock.sourceMatrix a)

theorem plus_restriction (a : ScalarIndex) :
    (sourceMatrix a).submatrix Sum.inl Sum.inl = SourceScalarFock.sourceMatrix a := rfl

theorem conjugate_restriction (a : ScalarIndex) :
    (sourceMatrix a).submatrix Sum.inr Sum.inr =
      -((SourceScalarFock.sourceMatrix a).map star) := rfl

theorem mixed_restrictions (a : ScalarIndex) :
    (sourceMatrix a).submatrix Sum.inl Sum.inr = 0 ∧
      (sourceMatrix a).submatrix Sum.inr Sum.inl = 0 := ⟨rfl, rfl⟩

abbrev FermionEnd := Module.End ℂ (Fock BranchIndex)
abbrev BosonEnd := SourceScalarCCR.BosonEnd ScalarIndex
abbrev JointAlgebra := BosonEnd ⊗[ℂ] FermionEnd
abbrev JointSpace := SourceScalarCCR.BosonSpace ScalarIndex ⊗[ℂ] Fock BranchIndex

def represent : JointAlgebra →ₐ[ℂ] Module.End ℂ JointSpace := Module.endTensorEndAlgHom

def density (a : ScalarIndex) : FermionEnd := Fermion.quantize (sourceMatrix a)

def coupling : JointAlgebra :=
  ∑ a : ScalarIndex, SourceScalarCCR.position a ⊗ₜ[ℂ] density a

def bosonMomentum (a : ScalarIndex) : JointAlgebra :=
  SourceScalarCCR.momentum a ⊗ₜ[ℂ] (1 : FermionEnd)

def rawPrimalPlus (i : Quantum.Index) : FermionEnd :=
  (Real.sqrt 2 : ℂ) • Fermion.annihilation (Sum.inl i)
def rawPrimalConjugate (i : Quantum.Index) : FermionEnd :=
  (Real.sqrt 2 : ℂ) • Fermion.annihilation (Sum.inr i)
def rawMomentumPlus (i : Quantum.Index) : FermionEnd :=
  (Real.sqrt 2 : ℂ) • Fermion.creation (Sum.inl i)
def rawMomentumConjugate (i : Quantum.Index) : FermionEnd :=
  (-(Real.sqrt 2 : ℂ)) • Fermion.creation (Sum.inr i)

private theorem sqrt_two_mul : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  norm_cast
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem negative_smul (c : ℂ) (A : FermionEnd) : (-c) • A = -(c • A) :=
  neg_smul c A

theorem density_two_branches (a : ScalarIndex) :
    density a =
      (∑ i : Quantum.Index, ∑ j : Quantum.Index,
        SourceScalarFock.sourceMatrix a i j •
          (Fermion.creation (Sum.inl i) * Fermion.annihilation (Sum.inl j))) -
      (∑ i : Quantum.Index, ∑ j : Quantum.Index,
        star (SourceScalarFock.sourceMatrix a i j) •
          (Fermion.creation (Sum.inr i) * Fermion.annihilation (Sum.inr j))) := by
  simp [density, Fermion.quantize, sourceMatrix, branches, Fintype.sum_sum_type,
    Matrix.fromBlocks, negative_smul, sub_eq_add_neg]

def rawRealCurrent (a : ScalarIndex) : FermionEnd :=
  (1 / 2 : ℂ) • ∑ i : Quantum.Index, ∑ j : Quantum.Index,
    (SourceScalarFock.sourceMatrix a i j • (rawMomentumPlus i * rawPrimalPlus j) +
      star (SourceScalarFock.sourceMatrix a i j) •
        (rawMomentumConjugate i * rawPrimalConjugate j))

theorem original_half_normalization (a : ScalarIndex) : rawRealCurrent a = density a := by
  rw [density_two_branches]
  simp only [rawRealCurrent, rawMomentumPlus, rawPrimalPlus, rawMomentumConjugate,
    rawPrimalConjugate, smul_mul_smul, neg_mul, sqrt_two_mul,
    Finset.smul_sum, smul_add, smul_smul]
  have scale (c : ℂ) : (1 / 2 : ℂ) * (c * 2) = c := by ring
  have negative (c : ℂ) : (1 / 2 : ℂ) * (c * -2) = -c := by ring
  simp only [scale, negative, negative_smul, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, sub_eq_add_neg]

theorem unit_branch_CAR (i j : BranchIndex) :
    Fermion.annihilation i * Fermion.creation j +
      Fermion.creation j * Fermion.annihilation i =
      (if i = j then 1 else 0 : ℂ) • (1 : FermionEnd) := by
  rw [Fermion.operator_car]
  split <;> simp_all

theorem plus_unit_CAR (i j : Quantum.Index) :
    Fermion.annihilation (Sum.inl i : BranchIndex) * Fermion.creation (Sum.inl j) +
      Fermion.creation (Sum.inl j) * Fermion.annihilation (Sum.inl i) =
      (if i = j then 1 else 0 : ℂ) • (1 : FermionEnd) := by
  simpa only [Sum.inl.injEq] using unit_branch_CAR (Sum.inl i) (Sum.inl j)

def plusWave (u : Quantum.Index → ℂ) : BranchIndex → ℂ := Sum.elim u 0

theorem source_plus_wave (a : ScalarIndex) (u : DiracExteriorMatterCarrier) :
    sourceMatrix a *ᵥ plusWave (Quantum.coordinates u) =
      plusWave (Quantum.coordinates
        (FullQuantum.yukawaHamiltonian (SourceScalarFock.scalarDirection a) u)) := by
  rw [sourceMatrix, branches, Matrix.fromBlocks_mulVec]
  simp only [plusWave, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero]
  rw [SourceScalarFock.sourceMatrix, Quantum.matrix_action]

set_option backward.isDefEq.respectTransparency false in
theorem original_plus_oneParticle (a : ScalarIndex) (u : DiracExteriorMatterCarrier) :
    density a (oneParticle (plusWave (Quantum.coordinates u))) =
      oneParticle (plusWave (Quantum.coordinates
        (FullQuantum.yukawaHamiltonian (SourceScalarFock.scalarDirection a) u))) := by
  rw [density, Fermion.quantize_apply, secondQuantize_oneParticle]
  change oneParticle (sourceMatrix a *ᵥ plusWave (Quantum.coordinates u)) = _
  rw [source_plus_wave]

theorem coupling_source_plus_oneParticle (u : DiracExteriorMatterCarrier) :
    represent coupling ((1 : SourceScalarCCR.BosonSpace ScalarIndex) ⊗ₜ[ℂ]
      oneParticle (plusWave (Quantum.coordinates u))) =
      ∑ a : ScalarIndex, MvPolynomial.X a ⊗ₜ[ℂ]
        oneParticle (plusWave (Quantum.coordinates
          (FullQuantum.yukawaHamiltonian (SourceScalarFock.scalarDirection a) u))) := by
  simp only [coupling, map_sum, LinearMap.sum_apply, represent,
    Module.endTensorEndAlgHom_apply, TensorProduct.AlgebraTensorModule.map_tmul,
    SourceScalarCCR.position_apply, mul_one, original_plus_oneParticle]

private theorem joint_sum_sub (f g : ScalarIndex → JointAlgebra) :
    (∑ a, f a) - (∑ a, g a) = ∑ a, (f a - g a) :=
  (Finset.sum_sub_distrib f g).symm

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
  · intro b _ different; exact if_neg different
  · intro absent; exact (absent (Finset.mem_univ a)).elim

theorem original_real_scalar_force (a : ScalarIndex) :
    Complex.I • (coupling * bosonMomentum a - bosonMomentum a * coupling) =
      -((1 : BosonEnd) ⊗ₜ[ℂ] rawRealCurrent a) := by
  rw [original_half_normalization, coupling_bosonMomentum, smul_smul, Complex.I_mul_I]
  exact neg_one_smul ℂ ((1 : BosonEnd) ⊗ₜ[ℂ] density a)

def complexBilinear (W : Matrix Quantum.Index Quantum.Index ℂ)
    (p ψ : Quantum.Index → ℂ) : ℂ := ∑ i, ∑ j, p i * W i j * ψ j

theorem real_current_half (W : Matrix Quantum.Index Quantum.Index ℂ)
    (p ψ : Quantum.Index → ℂ) :
    ((complexBilinear W p ψ).re : ℂ) =
      (1 / 2 : ℂ) * (complexBilinear W p ψ +
        complexBilinear (W.map star) (fun i => star (p i)) (fun i => star (ψ i))) := by
  rw [Complex.re_eq_add_conj]
  simp only [complexBilinear, map_sum, map_mul, Matrix.map_apply, starRingEnd_apply]
  ring

def branchScale : ℂ := (Real.sqrt 2 : ℂ)⁻¹

private theorem branchScale_square : branchScale * branchScale = 1 / 2 := by
  rw [branchScale, ← mul_inv_rev, sqrt_two_mul]
  norm_num

def normalizedPrimal (ψ : Quantum.Index → ℂ) : BranchIndex → ℂ :=
  Sum.elim (fun i => branchScale * ψ i) (fun i => branchScale * star (ψ i))

def normalizedMomentum (p : Quantum.Index → ℂ) : BranchIndex → ℂ :=
  Sum.elim (fun i => branchScale * p i) (fun i => -(branchScale * star (p i)))

theorem branches_original_real_bilinear (W : Matrix Quantum.Index Quantum.Index ℂ)
    (p ψ : Quantum.Index → ℂ) :
    (∑ i : BranchIndex, ∑ j : BranchIndex,
      normalizedMomentum p i * branches W i j * normalizedPrimal ψ j) =
      ((complexBilinear W p ψ).re : ℂ) := by
  rw [real_current_half]
  simp only [Fintype.sum_sum_type, normalizedPrimal, normalizedMomentum, branches,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, Matrix.neg_apply, Matrix.map_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul_neg]
  have scaled (x y z : ℂ) : (branchScale * x) * y * (branchScale * z) =
      (1 / 2 : ℂ) * (x * y * z) := by
    calc
      _ = (branchScale * branchScale) * (x * y * z) := by ring
      _ = _ := by rw [branchScale_square]
  simp_rw [scaled]
  simp only [complexBilinear, Matrix.map_apply, mul_add, Finset.mul_sum]

theorem original_legendre_bilinear (a : ScalarIndex) (point : BasePoint)
    (χ : Module.Dual ℂ DiracExteriorMatterCarrier) (ψ : DiracExteriorMatterCarrier) :
    FullQuantum.normalizedMomentum actual point χ
        (FullQuantum.yukawaHamiltonian (SourceScalarFock.scalarDirection a) ψ) =
      -((|(actual.coframe point).det| : ℝ) : ℂ) *
        χ (diracDualRightChiralYukawaAction (SourceScalarFock.scalarDirection a) ψ) := by
  have temporal : currentCoframeMatterTemporalPrincipal (actual.coframe point)
      ((-Complex.I) • FullQuantum.yukawaHamiltonian (SourceScalarFock.scalarDirection a) ψ) +
      diracDualRightChiralYukawaAction (SourceScalarFock.scalarDirection a) ψ = 0 := by
    rw [FullQuantum.actual_temporal_principal]
    exact SourceScalarFock.original_temporal_equation a ψ
  have equation := congrArg χ temporal
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at equation
  simp only [FullQuantum.normalizedMomentum, LinearMap.smul_apply,
    LinearMap.comp_apply, smul_eq_mul]
  linear_combination ((|(actual.coframe point).det| : ℝ) : ℂ) * equation

theorem original_real_source (a : ScalarIndex) (point : BasePoint)
    (χ : Module.Dual ℂ DiracExteriorMatterCarrier) (ψ : DiracExteriorMatterCarrier) :
    (FullQuantum.normalizedMomentum actual point χ
      (FullQuantum.yukawaHamiltonian (SourceScalarFock.scalarDirection a) ψ)).re =
      -Exchange.yukawaSource (actual.coframe point) ψ χ
        (scalarCoordinateEquiv (SourceScalarFock.scalarDirection a)) := by
  rw [original_legendre_bilinear]
  simp [Exchange.yukawaSource]

theorem source_complexBilinear (a : ScalarIndex) (point : BasePoint)
    (χ : Module.Dual ℂ DiracExteriorMatterCarrier) (ψ : DiracExteriorMatterCarrier) :
    complexBilinear (SourceScalarFock.sourceMatrix a)
      (Quantum.dualCoordinates (FullQuantum.normalizedMomentum actual point χ))
      (Quantum.coordinates ψ) =
      FullQuantum.normalizedMomentum actual point χ
        (FullQuantum.yukawaHamiltonian (SourceScalarFock.scalarDirection a) ψ) := by
  rw [Quantum.full_response]
  simp only [complexBilinear, SourceScalarFock.sourceMatrix, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_assoc]

theorem original_real_action_branches (a : ScalarIndex) (point : BasePoint)
    (χ : Module.Dual ℂ DiracExteriorMatterCarrier) (ψ : DiracExteriorMatterCarrier) :
    (∑ i : BranchIndex, ∑ j : BranchIndex,
      normalizedMomentum
        (Quantum.dualCoordinates (FullQuantum.normalizedMomentum actual point χ)) i *
      sourceMatrix a i j * normalizedPrimal (Quantum.coordinates ψ) j) =
      -((Exchange.yukawaSource (actual.coframe point) ψ χ
        (scalarCoordinateEquiv (SourceScalarFock.scalarDirection a)) : ℝ) : ℂ) := by
  rw [sourceMatrix, branches_original_real_bilinear, source_complexBilinear,
    original_real_source, Complex.ofReal_neg]

end
end SourceRealScalarFock
