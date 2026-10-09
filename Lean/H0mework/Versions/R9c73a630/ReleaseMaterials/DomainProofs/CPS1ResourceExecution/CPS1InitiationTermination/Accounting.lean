import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deamination.AtomicExecution

set_option autoImplicit false

namespace CPS1InitiationTermination.Accounting
open CPS1ResourceExecution

inductive Subunit | small | large deriving DecidableEq, Repr

def actorCount (actor : Actor) : Species → Nat
  | .actor other => if other = actor then 1 else 0
  | .terminatingInitiator | .terminatingPeptidyl _
  | .postTerminationInitiator | .postTerminationElongator _ => if Actor.eRF1 = actor then 1 else 0
  | _ => 0

def subunitCount (subunit : Subunit) : Species → Nat
  | .subunit40 | .initiator48S => if subunit = .small then 1 else 0
  | .subunit60 => if subunit = .large then 1 else 0
  | .ribosome80 | .terminatingInitiator | .terminatingPeptidyl _
  | .postTerminationInitiator | .postTerminationElongator _ => 1
  | _ => 0

def initiatorCount : Species → Nat
  | .initiatorTRNA | .chargedInitiator | .initiator48S | .initiatorPSite
  | .initiatorASite _ | .initiatorPreTranslocation _
  | .terminatingInitiator | .postTerminationInitiator => 1
  | _ => 0

theorem reaction_actor_balance (reaction : Reaction) (actor : Actor) :
    moiety (actorCount actor) reaction.reactants = moiety (actorCount actor) reaction.products := by
  cases reaction <;> simp [moiety, actorCount, Reaction.reactants, Reaction.products, factorStock]

theorem reaction_subunit_balance (reaction : Reaction) (subunit : Subunit) :
    moiety (subunitCount subunit) reaction.reactants = moiety (subunitCount subunit) reaction.products := by
  cases reaction <;> cases subunit <;>
    simp [moiety, subunitCount, Reaction.reactants, Reaction.products, factorStock]

theorem reaction_initiator_balance (reaction : Reaction) :
    moiety initiatorCount reaction.reactants = moiety initiatorCount reaction.products := by
  cases reaction <;> simp [moiety, initiatorCount, Reaction.reactants, Reaction.products, factorStock]

theorem execution_actor_balance (program : List Reaction) (stock : Stock) (actor : Actor) :
    moiety (actorCount actor) stock = moiety (actorCount actor) (execute program stock).stock :=
  CPS1Deamination.execution_measure_preserved program stock (actorCount actor)
    (fun reaction _ => reaction_actor_balance reaction actor)

theorem execution_subunit_balance (program : List Reaction) (stock : Stock) (subunit : Subunit) :
    moiety (subunitCount subunit) stock = moiety (subunitCount subunit) (execute program stock).stock :=
  CPS1Deamination.execution_measure_preserved program stock (subunitCount subunit)
    (fun reaction _ => reaction_subunit_balance reaction subunit)

theorem execution_initiator_balance (program : List Reaction) (stock : Stock) :
    moiety initiatorCount stock = moiety initiatorCount (execute program stock).stock :=
  CPS1Deamination.execution_measure_preserved program stock initiatorCount
    (fun reaction _ => reaction_initiator_balance reaction)

end CPS1InitiationTermination.Accounting
