import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.BathAccounting

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing
variable {frame : CPS1Recycling.Frame}

theorem native_reactants_no_ammonia (reaction : Reaction) : reaction.reactants.count Species.ammonia = 0 := by
  cases reaction <;> simp [Reaction.reactants,factorStock]

theorem native_ammonia_retained (program : List Reaction) (stock : Stock) :
    stock.count Species.ammonia ≤ (execute program stock).stock.count Species.ammonia := by
  have balance := execution_balance program stock Species.ammonia
  have debited := CPS1EnzymeBath.BathAccounting.trace_count_zero Reaction.reactants Species.ammonia
    native_reactants_no_ammonia (execute program stock).fired
  change (debit (execute program stock).fired).count Species.ammonia = 0 at debited
  rw [debited,Nat.add_zero] at balance
  omega

theorem actual_translation_ammonia_retained {current : CPS1ReactiveField.Occurrence frame}
    {water : Nat} {raw : List RawSupply} (event : TranslationEvent current water raw) :
    (liveResources current).count Species.ammonia ≤ event.native.stock.count Species.ammonia := by
  have retained := native_ammonia_retained event.program event.available
  rw [← event.actual] at retained
  have stock := event.availableSource
  have input : event.available.count Species.ammonia =
      event.genomic.event.result.stock.count Species.ammonia+(raw.map RawSupply.species).count Species.ammonia := by
    rw [stock,List.count_append]
  rw [event.genomic.ammonia] at input
  omega

end
end CPS1SameEventFunction
