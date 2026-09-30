import H0mework.Realization.Audit.U7Coface

/-!
# Regression for the free residual-world coface

The old obstruction language is empty.  Two residual coordinates still
generate distinct obstructions, exact causal rows, a transported-theory
expressibility failure and the existing U7 theory-audit branch.  This is the
negative fixture that forbids treating `N.ObstructionAt` as a premise of
generic residual admission.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedResidualAdmissionRegression

open RootGeneratedResidualAdmission

def oldNetwork : WorldRelationNetwork where
  Support := Unit
  Anchor := Unit
  Incidence := Unit
  Lineage := Unit
  Responsibility := Unit
  Claim := Unit
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := fun _ => ()
  OpenAt := fun _ _ => Unit
  openClaimAt := fun _ => ()
  HoldsAt := fun _ _ => Unit
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := PEmpty.elim
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := fun _ _ => Unit

abbrev OldN := oldNetwork
abbrev NewN := ExtendedNetwork OldN () Bool

def oldU7 : U7ProducerCalculus OldN where
  DemandAt := by
    intro support obstruction
    exact nomatch obstruction
  generateDemand := by
    intro support obstruction
    exact nomatch obstruction

def oldU7Source : U7ActualSuccessorSource OldN oldU7 where
  EventAt := by
    intro support obstruction demand
    exact nomatch obstruction
  emit := by
    intro support obstruction
    exact nomatch obstruction
  demandGeneratedAt := by
    intro support obstruction demand event
    exact nomatch obstruction
  demandEntryAt := by
    intro support obstruction demand event
    exact nomatch obstruction

def oldCalculus : U7ObstructionEvolutionCalculus OldN oldU7 where
  source := oldU7Source
  compile := by
    intro support obstruction demand event
    exact nomatch obstruction

theorem old_obstruction_language_is_empty :
    IsEmpty (OldN.ObstructionAt ()) :=
  ⟨fun obstruction => nomatch obstruction⟩

theorem old_language_has_no_residual_exposure :
    IsEmpty (Bool → OldN.ObstructionAt ()) :=
  ⟨fun alleged => nomatch alleged false⟩

theorem new_residual_obstructions_are_distinct :
    residualObstruction (N := OldN) () false ≠
      residualObstruction (N := OldN) () true := by
  intro equality
  exact Bool.false_ne_true
    (residualObstruction_injective (N := OldN) () Bool equality)

theorem new_residual_row_claim_is_exact :
    (residualEntry (N := OldN) () true).claim =
      NewN.obstructionClaim (residualObstruction (N := OldN) () true) :=
  rfl

def oldTheory : TheoryState OldN := TheoryState.rootSemantic OldN

def generatedFailure : ActualExpressibilityFailure
    (liftTheory () (Residual := Bool) oldTheory)
    (residualObstruction (N := OldN) () true) :=
  residualFailure () oldTheory true

theorem generated_u7_row_is_residual_row :
    U7ActualSuccessorSource.demandEntry
        ((extendU7Calculus () oldU7 oldCalculus).source.emit
          (residualObstruction (N := OldN) () true)) =
      residualEntry (N := OldN) () true :=
  residual_u7_demand_entry () oldU7 oldCalculus true

def generatedTheoryAudit :
    SourceNativeU7TheoryAuditAt
      (extendU7Calculus () oldU7 oldCalculus)
      ((extendU7Calculus () oldU7 oldCalculus).source.emit
        (residualObstruction (N := OldN) () true)) :=
  residual_u7_theoryAudit () oldU7 oldCalculus true

theorem free_claim_extension_is_unique
    (candidate : NewN.Claim → Nat)
    (old_eq : (claim : OldN.Claim) → candidate (.inl claim) = 0)
    (residual_eq : (coordinate : Bool) →
      candidate (.inr coordinate) = if coordinate then 1 else 2)
    (claim : NewN.Claim) :
    candidate claim =
      claimLift (focus := ()) (fun _ => 0)
        (fun coordinate => if coordinate then 1 else 2) claim :=
  claimLift_unique (focus := ()) _ _ candidate old_eq residual_eq claim

#print axioms old_language_has_no_residual_exposure
#print axioms new_residual_obstructions_are_distinct
#print axioms generatedFailure
#print axioms generated_u7_row_is_residual_row
#print axioms generatedTheoryAudit
#print axioms free_claim_extension_is_unique

end RootGeneratedResidualAdmissionRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
