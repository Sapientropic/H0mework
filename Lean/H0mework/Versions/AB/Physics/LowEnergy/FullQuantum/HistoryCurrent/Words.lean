import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.SpatialCARState

/-! One common finite test span reads the complete ordered current insertion, with an independent dual. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
open MatterSpace.SpatialCAR
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def commutatorTests (boundary reader force : E →L[ℂ] E) (dual initial : E) : Fin 4 → E :=
  ![reader.adjoint (boundary.adjoint dual),force initial,
    force.adjoint (boundary.adjoint dual),reader initial]

def commutatorCAR (boundary reader force : E →L[ℂ] E) (dual initial : E) : ℂ :=
  spatialMoment initial (commutatorTests boundary reader force dual initial)
      [.create none,.annihilate (some 0),.create (some 1),.annihilate none]-
    spatialMoment initial (commutatorTests boundary reader force dual initial)
      [.create none,.annihilate (some 2),.create (some 3),.annihilate none]

theorem commutatorCAR_read (boundary reader force : E →L[ℂ] E) (dual initial : E) (unit : ‖initial‖=1) :
    commutatorCAR boundary reader force dual initial=
      inner ℂ dual (boundary (reader (force initial)-force (reader initial))) := by
  simp [commutatorCAR,spatialMoment_fourPoint,family,commutatorTests,unit,
    ContinuousLinearMap.adjoint_inner_left]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
