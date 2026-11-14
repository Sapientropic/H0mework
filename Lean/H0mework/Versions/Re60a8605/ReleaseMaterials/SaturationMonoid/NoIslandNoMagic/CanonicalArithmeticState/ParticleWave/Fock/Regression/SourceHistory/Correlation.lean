import H0mework.Probability.FullSource.Word
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.GenericFoundation.Probability.Source.Full.Binary
import H0mework.Fock.SourceHistory.Installed

/-! Equal marginal source words do not determine the result of an actual binary operation. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FullBinary.Controls

open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open ArithmeticGeneration
open SourceGeneratedActionObservationHistory

noncomputable section

def first : Current := (runtimeAt 0).current.visit.current
def second : Current := (runtimeAt 1).current.visit.current

def diagonal : Carrier (Current × Current) := sourcePoint (first, first) + sourcePoint (second, second)
def crossed : Carrier (Current × Current) := sourcePoint (first, second) + sourcePoint (second, first)

theorem marginals_equal :
    Finsupp.lmapDomain ℤ ℤ Prod.fst diagonal = Finsupp.lmapDomain ℤ ℤ Prod.fst crossed ∧
      Finsupp.lmapDomain ℤ ℤ Prod.snd diagonal = Finsupp.lmapDomain ℤ ℤ Prod.snd crossed := by
  simp only [diagonal, crossed, map_add, sourcePoint, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact ⟨True.intro, add_comm _ _⟩

theorem operation_distinguishes_joint :
    SourceNativeBinary.pushJoint UnitHistory.parallel diagonal ≠
      SourceNativeBinary.pushJoint UnitHistory.parallel crossed := by
  intro same
  have coefficient := congrArg (fun value : Carrier Current => value (UnitHistory.parallel first first)) same
  simp only [diagonal, crossed, map_add, sourcePoint, SourceNativeBinary.pushJoint_point,
    Finsupp.add_apply] at coefficient
  change ((Finsupp.single (UnitHistory.next (.next .empty)) (1 : ℤ) +
      Finsupp.single (UnitHistory.next (.next (.next (.next .empty)))) 1) : Carrier Current) (.next (.next .empty)) =
    ((Finsupp.single (UnitHistory.next (.next (.next .empty))) 1 +
      Finsupp.single (UnitHistory.next (.next (.next .empty))) 1) : Carrier Current) (.next (.next .empty)) at coefficient
  simp at coefficient

theorem full_field_operation_distinguishes_joint :
    pushJoint nativeStep nativeStep nativeStep UnitHistory.parallel
        (sourceMap (sourceAction (Prod.map nativeStep nativeStep)) (observation sourcePoint) diagonal) ≠
      pushJoint nativeStep nativeStep nativeStep UnitHistory.parallel
        (sourceMap (sourceAction (Prod.map nativeStep nativeStep)) (observation sourcePoint) crossed) := by
  intro same
  rw [pushJoint_source, pushJoint_source] at same
  exact operation_distinguishes_joint (full_sourceMap_injective nativeStep same)

end
end SourceOwnedObservationHistory.FullBinary.Controls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
