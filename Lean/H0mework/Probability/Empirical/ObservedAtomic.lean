import H0mework.Probability.Recovery.AtomicReader
import H0mework.Probability.Empirical.ObservedRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAtomicObservation.Runtime

open SourceGeneratedEmpiricalHilbert SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability SourceConditionalTransfer
open SourceGeneratedScalarDifferentialResidual
open scoped InnerProductSpace

noncomputable section

variable {N : WorldRelationNetwork.{0}} {process : SourceNativeLivingRootProcess N}
variable {B : Type} [AddCommGroup B] (read : process.State → B) (bound : Nat) (index : Fin (bound + 1))

local instance atomFieldUniform : UniformSpace (Field read) := fieldUniform read
local instance atomFieldMeasurable : MeasurableSpace (Field read) := fieldBorel read
local instance atomFieldBorel : BorelSpace (Field read) := ⟨rfl⟩
local instance atomFieldT2 : T2Space (Field read) := field_t2 read

def cotestAt (runtime : LivingRuntimeState process) : Space read runtime bound :=
  covector (fieldPMF read runtime bound) (fieldSample read runtime bound index)

theorem atom_supported (runtime : LivingRuntimeState process) :
    fieldSample read runtime bound index ∈ (fieldPMF read runtime bound).support :=
  (fieldPMF_support_iff read runtime bound _).mpr ⟨index, rfl⟩

theorem reader_original (runtime : LivingRuntimeState process) :
    (innerSL ℂ (cotestAt read bound index runtime)).toLinearMap =
      SourceWeightedRecovery.evalAt (fieldPMF read runtime bound) (fieldSample read runtime bound index)
        (atom_supported read bound index runtime) := by
  ext value
  exact covector_read _ _ (atom_supported read bound index runtime) value

theorem next_conditional (runtime : LivingRuntimeState process) (value : Space read runtime bound) :
    SourceGeneratedActionObservationHistory.Dependent.Runtime.reader read bound (cotestAt read bound index) runtime.tick.next
        (SourceGeneratedActionObservationHistory.Dependent.Runtime.next read bound (cotestAt read bound index) runtime
          (canonicalResidual (SourceGeneratedActionObservationHistory.Dependent.Runtime.source read bound
            (cotestAt read bound index) runtime) value)) =
      conditionalValue read runtime bound value (nextAtom read runtime bound index)
        (SourceGeneratedActionObservationHistory.Dependent.Runtime.nextAtom_supported read bound runtime index) := by
  have generated := SourceGeneratedActionObservationHistory.Dependent.Runtime.next_read
    (process := process) read bound (cotestAt read bound index) runtime value
  have actual := covector_read (fieldPMF read runtime.tick.next bound)
    (fieldSample read runtime.tick.next bound index) (atom_supported read bound index runtime.tick.next)
    (transfer read runtime bound value)
  have pointRead : transfer read runtime bound value (fieldSample read runtime.tick.next bound index) =
      conditionalValue read runtime bound value (nextAtom read runtime bound index)
        (SourceGeneratedActionObservationHistory.Dependent.Runtime.nextAtom_supported read bound runtime index) := by
    rw [← nextAtom_eq_next_sample]
    exact transfer_at_atom read runtime bound value _ _
  exact generated.trans (actual.trans pointRead)

end
end SourceGeneratedAtomicObservation.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
