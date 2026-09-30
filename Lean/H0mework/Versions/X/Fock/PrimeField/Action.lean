import H0mework.Versions.X.Fock.PrimeField.Projection

/-! The original native write supplies two new factorial factors before the original Fock field increment is read. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFactorizationAction.Fock

open ArithmeticGeneration CanonicalUnitArithmeticFactorizationOccurrence
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime

noncomputable section

def history (current : CanonicalUnitArithmeticRoot.Current) : UnitHistory :=
  ownerEvenTargetHistory (liveGlobalOwner current) (scanIndex current)

theorem history_size (current : CanonicalUnitArithmeticRoot.Current) :
    (history current).cardinalShadow = 2 * (scanIndex current + 1) := by
  rw [history, ownerEvenTargetHistory_eq_generate, UnitHistory.cardinalShadow_generate]

theorem history_next (current : CanonicalUnitArithmeticRoot.Current) :
    history (CanonicalUnitArithmeticRoot.next current) = (history current).next.next := by
  apply UnitHistory.eq_of_cardinalShadow_eq
  change (history (CanonicalUnitArithmeticRoot.next current)).cardinalShadow =
    (history current).cardinalShadow + 1 + 1
  rw [history_size, history_size, scanIndex_next]
  omega

def wholeIncrement (current : CanonicalUnitArithmeticRoot.Current) : Nat.Primes →₀ Nat :=
  primeIncrement (history current) + primeIncrement (history current).next

theorem counts_next (current : CanonicalUnitArithmeticRoot.Current) :
    primeCounts (history (CanonicalUnitArithmeticRoot.next current)) =
      primeCounts (history current) + wholeIncrement current := by
  rw [history_next, prime_step, prime_step, add_assoc]
  rfl

def birth (current : CanonicalUnitArithmeticRoot.Current) : IntegralOneParticle :=
  SourceSupportAction.born atom (primeCounts (history current)) (wholeIncrement current)

theorem field_read (current : CanonicalUnitArithmeticRoot.Current) :
    sourceFieldAt current = supportProjection (primeCounts (history current)) :=
  owner_field_is_projection (liveGlobalOwner current) (scanIndex current)

theorem field_next (current : CanonicalUnitArithmeticRoot.Current) :
    sourceFieldAt (CanonicalUnitArithmeticRoot.next current) = sourceFieldAt current + birth current := by
  calc
    _ = supportProjection (primeCounts (history (CanonicalUnitArithmeticRoot.next current))) := field_read _
    _ = supportProjection (primeCounts (history current) + wholeIncrement current) :=
      congrArg supportProjection (counts_next current)
    _ = supportProjection (primeCounts (history current)) + birth current :=
      SourceSupportAction.read_update atom (primeCounts (history current)) (wholeIncrement current)
    _ = _ := congrArg (fun value => value + birth current) (field_read current).symm

theorem target_field (current : CanonicalUnitArithmeticRoot.Current) :
    targetFieldAt current = sourceFieldAt current + birth current := field_next current

variable {current : CanonicalUnitArithmeticRoot.Current}
variable {occurrence : BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
variable {active : 1 ≤ scanIndex current}

theorem installed_increment (payload : RootGeneratedParticleWaveCurrentAt current occurrence active) :
    sourceFieldAt payload.nativeWrite.target - sourceFieldAt current = birth current := by
  rw [payload.nativeWrite.target_eq, field_next, add_sub_cancel_left]

end
end SourceFactorizationAction.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
