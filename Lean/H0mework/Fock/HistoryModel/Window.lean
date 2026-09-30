import H0mework.Probability.Source.ModelRestriction
import H0mework.Fock.HistoryCopy.Installed

/-! The entire actual past-actor inventory generates one observation model and its native extension. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FamilyModel.Fock

open SourceGeneratedActionObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime

noncomputable section

abbrev Index (depth : Nat) := Fin (NativeWindow.bound (runtimeAt depth).current.visit.current + 1)

def reader (depth : Nat) (index : Index depth) (state : Current) : ParentCarrier :=
  sourceStateAt (NativeCopy.copy (NativeCopy.Fock.material depth index) state)

abbrev WholeModel (depth : Nat) :=
  Model (sourceAction nativeStep) (observation (familyRead (reader depth)))

def point (depth : Nat) (state : Current) : WholeModel depth :=
  projection (sourceAction nativeStep) (observation (familyRead (reader depth))) (sourcePoint state)

def action (depth : Nat) : WholeModel depth →ₗ[ℤ] WholeModel depth :=
  modelAction (sourceAction nativeStep) (observation (familyRead (reader depth)))

def readout (depth : Nat) : WholeModel depth →ₗ[ℤ] (Index depth → ParentCarrier) :=
  modelReadout (sourceAction nativeStep) (observation (familyRead (reader depth)))

def oldIndex (depth : Nat) (index : Index depth) : Index (depth + 1) :=
  ⟨index.val, by
    have oldBound := runtime_bound depth
    have newBound := runtime_bound (depth + 1)
    have inside := index.isLt
    omega⟩

theorem reader_oldIndex (depth : Nat) (index : Index depth) :
    reader (depth + 1) (oldIndex depth index) = reader depth index := rfl

def forgetLast (depth : Nat) : WholeModel (depth + 1) →ₗ[ℤ] WholeModel depth :=
  restriction nativeStep (reader (depth + 1)) (oldIndex depth)

theorem forgetLast_surjective (depth : Nat) : Function.Surjective (forgetLast depth) :=
  restriction_surjective nativeStep (reader (depth + 1)) (oldIndex depth)

theorem forgetLast_point (depth : Nat) (state : Current) :
    forgetLast depth (point (depth + 1) state) = point depth state :=
  restriction_projection nativeStep (reader (depth + 1)) (oldIndex depth) (sourcePoint state)

theorem forgetLast_action (depth : Nat) (value : WholeModel (depth + 1)) :
    forgetLast depth (action (depth + 1) value) = action depth (forgetLast depth value) :=
  restriction_action nativeStep (reader (depth + 1)) (oldIndex depth) value

theorem point_read (depth : Nat) (state : Current) (index : Index depth) :
    readout depth (point depth state) index = reader depth index state :=
  congrFun (sourcePoint_read nativeStep (reader depth) state) index

theorem point_action (depth : Nat) (state : Current) :
    action depth (point depth state) = point depth (nativeStep state) :=
  sourcePoint_action nativeStep (reader depth) state

end
end SourceOwnedObservationHistory.FamilyModel.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
