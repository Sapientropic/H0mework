import H0mework.Physics.LowEnergy.Quantum.ScalarFock

/-! Certifies the original complex-bilinear canonical component on its actual
tensor polynomial/CAR domain. The real scalar Euler source is separately
identified below; no independent-dual adjoint restriction is substituted. -/
set_option autoImplicit false
open SourceScalarFock
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction QuantizationCheck.Fermion
open scoped TensorProduct
noncomputable section
attribute [local instance] Fermion.fullIndexOrder

example (a : ScalarIndex) (state : JointSpace) :
    Complex.I • (represent coupling (represent (bosonMomentum a) state) -
      represent (bosonMomentum a) (represent coupling state)) =
    represent (-((1 : BosonEnd) ⊗ₜ[ℂ] density a) : JointAlgebra) state := by
  have identity := LinearMap.congr_fun
    (congrArg represent (boson_momentum_equation a)) state
  simpa only [map_smul, map_sub, map_mul,
    LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply] using identity

example (a b : ScalarIndex) (f : SourceScalarCCR.BosonSpace ScalarIndex)
    (u v : DiracExteriorMatterCarrier) :
    represent ((1 : BosonEnd) ⊗ₜ[ℂ] (density a * density b))
      (f ⊗ₜ[ℂ] Fermion.sourcePair u v) =
    f ⊗ₜ[ℂ] (Fermion.sourcePair
      (FullQuantum.yukawaHamiltonian (scalarDirection a) u)
      (FullQuantum.yukawaHamiltonian (scalarDirection b) v) -
      Fermion.sourcePair
      (FullQuantum.yukawaHamiltonian (scalarDirection a) v)
      (FullQuantum.yukawaHamiltonian (scalarDirection b) u)) := by
  simp only [represent, Module.endTensorEndAlgHom_apply,
    TensorProduct.AlgebraTensorModule.map_tmul, Module.End.one_apply,
    density_twoParticle]

#print axioms SourceScalarFock.scalar_index_card
#print axioms SourceScalarFock.full_real_scalar_reconstruction
#print axioms SourceScalarFock.density_original
#print axioms SourceScalarFock.coupling_tensor_action
#print axioms SourceScalarFock.coupling_source_oneParticle
#print axioms SourceScalarFock.annihilator_original
#print axioms SourceScalarFock.momentumCreator_original
#print axioms SourceScalarFock.independentDual_original
#print axioms SourceScalarFock.original_temporal_equation
#print axioms SourceScalarFock.coupling_bosonMomentum
#print axioms SourceScalarFock.boson_momentum_equation
#print axioms SourceScalarFock.coupling_bosonPosition
#print axioms SourceScalarFock.annihilator_coupling
#print axioms SourceScalarFock.quantize_momentumCreator
#print axioms SourceScalarFock.coupling_momentumCreator
#print axioms SourceScalarFock.canonical_CAR
#print axioms SourceScalarFock.source_matrix_product_zero
#print axioms SourceScalarFock.density_normal_order
#print axioms SourceScalarFock.density_twoParticle
#print axioms SourceScalarFock.coupling_square_normal_order
#print axioms Exchange.original_scalar_source
#print axioms Fermion.realVertex_response
#check SourceScalarFock.independentDual_original
#check SourceScalarFock.boson_momentum_equation
#check Exchange.yukawaSource
#check Exchange.original_scalar_source
#check Fermion.realVertex_response
