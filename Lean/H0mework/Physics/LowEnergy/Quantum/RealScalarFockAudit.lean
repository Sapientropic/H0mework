import H0mework.Physics.LowEnergy.Quantum.RealScalarFock

/-! Original independent-dual real source and its normalized branch consumer.
The plus unit generators and the unscaled original variables are distinct. -/
set_option autoImplicit false
open SourceRealScalarFock
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction QuantizationCheck.Fermion
open scoped TensorProduct
noncomputable section
attribute [local instance] Fermion.fullIndexOrder branchOrder

example (i : Quantum.Index) :
    rawPrimalPlus i * rawMomentumPlus i + rawMomentumPlus i * rawPrimalPlus i =
      (2 : ℂ) • (1 : FermionEnd) := by
  have square : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [rawPrimalPlus, rawMomentumPlus, smul_mul_smul, square,
    ← smul_add, plus_unit_CAR]
  simp

example (a : ScalarIndex) (state : JointSpace) :
    Complex.I • (represent coupling (represent (bosonMomentum a) state) -
      represent (bosonMomentum a) (represent coupling state)) =
      represent (-((1 : BosonEnd) ⊗ₜ[ℂ] rawRealCurrent a) : JointAlgebra) state := by
  have identity := LinearMap.congr_fun
    (congrArg represent (original_real_scalar_force a)) state
  simpa only [map_smul, map_sub, map_mul, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.mul_apply] using identity

#print axioms SourceRealScalarFock.plus_restriction
#print axioms SourceRealScalarFock.conjugate_restriction
#print axioms SourceRealScalarFock.mixed_restrictions
#print axioms SourceRealScalarFock.density_two_branches
#print axioms SourceRealScalarFock.original_half_normalization
#print axioms SourceRealScalarFock.unit_branch_CAR
#print axioms SourceRealScalarFock.plus_unit_CAR
#print axioms SourceRealScalarFock.source_plus_wave
#print axioms SourceRealScalarFock.original_plus_oneParticle
#print axioms SourceRealScalarFock.coupling_source_plus_oneParticle
#print axioms SourceRealScalarFock.coupling_bosonMomentum
#print axioms SourceRealScalarFock.original_real_scalar_force
#print axioms SourceRealScalarFock.real_current_half
#print axioms SourceRealScalarFock.branches_original_real_bilinear
#print axioms SourceRealScalarFock.original_legendre_bilinear
#print axioms SourceRealScalarFock.original_real_source
#print axioms SourceRealScalarFock.source_complexBilinear
#print axioms SourceRealScalarFock.original_real_action_branches
#check SourceRealScalarFock.original_real_action_branches
#check SourceRealScalarFock.original_half_normalization
#check SourceRealScalarFock.plus_unit_CAR
