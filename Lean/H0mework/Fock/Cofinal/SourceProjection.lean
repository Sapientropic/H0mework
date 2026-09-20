import H0mework.Arithmetic.FockDynamics.RootRuntime

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix

open ParticleWaveFock ParticleWaveFockRuntime SourceOperationEffects

noncomputable section

def sourceMaterial (state : process.State) : IntegralOneParticle :=
  sourceFieldAt (finiteVisit state).current

def environmentProjection : IntegralOneParticle →+ Env OperationValue OperationVar where
  toFun := fieldEnvironment
  map_zero' := by
    funext sort arg
    cases sort with
    | field => rfl
    | pair => exact PEmpty.elim arg
    | parent => exact PEmpty.elim arg
  map_add' := fun left right => (fieldEnvironment_add left right).symm

theorem sourceMaterial_is_actual (runtime : LivingRuntimeState process) :
    sourceMaterial runtime.state = sourceFieldAt runtime.current.visit.current := rfl

end
end NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
