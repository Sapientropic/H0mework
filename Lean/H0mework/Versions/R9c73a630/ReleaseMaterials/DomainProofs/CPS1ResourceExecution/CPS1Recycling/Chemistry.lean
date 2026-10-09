import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Recycling.Frame

set_option autoImplicit false

namespace CPS1Recycling
open CPS1ResourceExecution

inductive Nucleotide | empty | atp | adp deriving DecidableEq,Repr
structure Sites where
  first : Nucleotide
  second : Nucleotide
  deriving DecidableEq,Repr

def emptySites : Sites := ⟨.empty,.empty⟩
def doubleATP : Sites := ⟨.atp,.atp⟩
def humanHybrid : Sites := ⟨.adp,.atp⟩

inductive Trna | initiator | elongator (aa : AA) deriving DecidableEq,Repr

def sourceTrna (frame : Frame) : Trna :=
  match frame.peptide.2 with
  | [] => .initiator
  | _ :: _ => .elongator frame.peptide.last

def postSpecies : Trna → CPS1ResourceExecution.Species
  | .initiator => .postTerminationInitiator
  | .elongator aa => .postTerminationElongator aa

def returnedTrna : Trna → CPS1ResourceExecution.Species
  | .initiator => .initiatorTRNA
  | .elongator aa => .tRNA aa

/-- Every compound carries the same source message index; no RNA is reconstructed from a postTC label. -/
inductive Species (frame : Frame)
  | old (species : CPS1ResourceExecution.Species)
  | abce1 (sites : Sites) | eIF3j | adp
  | preSplit (trna : Trna) (sites : Sites)
  | boundSmall (trna : Trna) (sites : Sites)
  | smallWithMessage (sites : Sites)
  | primedSmall (sites : Sites)
  | next43 (sites : Sites)
  | messageCoordinate
  deriving DecidableEq

/-- Site-specific primitive inputs record ATP occupancy and individual ATPase events.
The sampled TT→DT path is not a claim of two hydrolyses per recycling cycle. -/
inductive Primitive
  | chargeNextInitiator
  | engageControl (trna : Trna)
  | engageWork (trna : Trna)
  | splitHydrolyzingFirst (trna : Trna)
  | splitHydrolyzingSecond (trna : Trna)
  | hydrolyzeFirst (trna : Trna) (second : Nucleotide)
  | removeTrna (trna : Trna) (sites : Sites)
  | removeMessage (sites : Sites)
  | captureNext (sites : Sites)
  deriving DecidableEq,Repr

namespace Primitive

def reactants (frame : Frame) : Primitive → List (Species frame)
  | .chargeNextInitiator => Reaction.chargeInitiator.reactants.map Species.old
  | .engageControl trna => [.old (postSpecies trna),.abce1 emptySites,.old .atp]
  | .engageWork trna => [.preSplit trna ⟨.empty,.atp⟩,.old .atp]
  | .splitHydrolyzingFirst trna | .splitHydrolyzingSecond trna => [.preSplit trna doubleATP,.old .water]
  | .hydrolyzeFirst trna second => [.boundSmall trna ⟨.atp,second⟩,.old .water]
  | .removeTrna trna sites => [.boundSmall trna sites,.old (.actor .eIF1),
      .old (.actor .eIF1A),.old (.actor .eIF3)]
  | .removeMessage sites => [.smallWithMessage sites,.eIF3j]
  | .captureNext sites => [.primedSmall sites,.old .chargedInitiator,.old .gtp,.old (.actor .eIF2)]

def products (frame : Frame) : Primitive → List (Species frame)
  | .chargeNextInitiator => Reaction.chargeInitiator.products.map Species.old
  | .engageControl trna => [.preSplit trna ⟨.empty,.atp⟩]
  | .engageWork trna => [.preSplit trna doubleATP]
  | .splitHydrolyzingFirst trna => [.boundSmall trna humanHybrid,.old .subunit60,.old (.actor .eRF1),
      .old .phosphate,.old .proton]
  | .splitHydrolyzingSecond trna => [.boundSmall trna ⟨.atp,.adp⟩,.old .subunit60,.old (.actor .eRF1),
      .old .phosphate,.old .proton]
  | .hydrolyzeFirst trna second => [.boundSmall trna ⟨.adp,second⟩,.old .phosphate,.old .proton]
  | .removeTrna trna sites => [.smallWithMessage sites,.old (returnedTrna trna)]
  | .removeMessage sites => [.primedSmall sites,.messageCoordinate]
  | .captureNext sites => [.next43 sites]
end Primitive

def nucleotideAdenylate : Nucleotide → Nat | .empty => 0 | .atp | .adp => 1
def nucleotidePhosphate : Nucleotide → Nat | .empty => 0 | .atp => 3 | .adp => 2

def siteMeasure (measure : Nucleotide → Nat) (sites : Sites) : Nat :=
  measure sites.first + measure sites.second

def adenylate (frame : Frame) : Species frame → Nat
  | .old species => CPS1ResourceExecution.adenylate species
  | .adp => 1
  | .abce1 sites | .preSplit _ sites | .boundSmall _ sites
  | .smallWithMessage sites | .primedSmall sites | .next43 sites => siteMeasure nucleotideAdenylate sites
  | _ => 0

def phosphate (frame : Frame) : Species frame → Nat
  | .old species => phosphateGroups species
  | .adp => 2
  | .next43 sites => siteMeasure nucleotidePhosphate sites + 3
  | .abce1 sites | .preSplit _ sites | .boundSmall _ sites
  | .smallWithMessage sites | .primedSmall sites => siteMeasure nucleotidePhosphate sites
  | _ => 0

def guanylate (frame : Frame) : Species frame → Nat
  | .old species => CPS1ResourceExecution.guanylate species
  | .next43 _ => 1
  | _ => 0

def abce1Count (frame : Frame) : Species frame → Nat
  | .abce1 _ | .preSplit _ _ | .boundSmall _ _ | .smallWithMessage _
  | .primedSmall _ | .next43 _ => 1
  | _ => 0

def trnaCount (frame : Frame) : Species frame → Nat
  | .old species => CPS1ResourceExecution.trnaCount species
  | .preSplit _ _ | .boundSmall _ _ | .next43 _ => 1
  | _ => 0

def smallCount (frame : Frame) : Species frame → Nat
  | .old species => CPS1InitiationTermination.Accounting.subunitCount .small species
  | .preSplit _ _ | .boundSmall _ _ | .smallWithMessage _ | .primedSmall _ | .next43 _ => 1
  | _ => 0

def largeCount (frame : Frame) : Species frame → Nat
  | .old species => CPS1InitiationTermination.Accounting.subunitCount .large species
  | .preSplit _ _ => 1
  | _ => 0

def moiety (frame : Frame) (measure : Species frame → Nat) (stock : List (Species frame)) : Nat :=
  (stock.map measure).sum

theorem primitive_currency_balance (frame : Frame) (primitive : Primitive) :
    moiety frame (adenylate frame) (primitive.reactants frame) =
      moiety frame (adenylate frame) (primitive.products frame) ∧
    moiety frame (guanylate frame) (primitive.reactants frame) =
      moiety frame (guanylate frame) (primitive.products frame) ∧
    moiety frame (phosphate frame) (primitive.reactants frame) =
      moiety frame (phosphate frame) (primitive.products frame) := by
  cases primitive <;>
    simp [moiety,Primitive.reactants,Primitive.products,Reaction.reactants,Reaction.products,adenylate,guanylate,phosphate,
      siteMeasure,nucleotideAdenylate,nucleotidePhosphate,emptySites,doubleATP,humanHybrid,
      CPS1ResourceExecution.adenylate,CPS1ResourceExecution.guanylate,phosphateGroups,
      postSpecies,returnedTrna]
  all_goals try cases ‹Trna›
  all_goals dsimp (config := {failIfUnchanged := false}) [postSpecies,returnedTrna,CPS1ResourceExecution.adenylate,
    CPS1ResourceExecution.guanylate,phosphateGroups]
  all_goals first | trivial | omega

theorem primitive_carrier_balance (frame : Frame) (primitive : Primitive) :
    moiety frame (abce1Count frame) (primitive.reactants frame) =
      moiety frame (abce1Count frame) (primitive.products frame) ∧
    moiety frame (trnaCount frame) (primitive.reactants frame) =
      moiety frame (trnaCount frame) (primitive.products frame) ∧
    moiety frame (smallCount frame) (primitive.reactants frame) =
      moiety frame (smallCount frame) (primitive.products frame) ∧
    moiety frame (largeCount frame) (primitive.reactants frame) =
      moiety frame (largeCount frame) (primitive.products frame) := by
  cases primitive <;>
    simp [moiety,Primitive.reactants,Primitive.products,Reaction.reactants,Reaction.products,abce1Count,trnaCount,smallCount,
      largeCount,CPS1ResourceExecution.trnaCount,CPS1InitiationTermination.Accounting.subunitCount,
      postSpecies,returnedTrna]
  all_goals cases ‹Trna›
  all_goals dsimp (config := {failIfUnchanged := false}) [postSpecies,returnedTrna,CPS1ResourceExecution.trnaCount,
    CPS1InitiationTermination.Accounting.subunitCount]
  all_goals trivial


inductive Factor
  | old (actor : Actor) | abce1 | eIF3j
  deriving DecidableEq,Repr

def actorCount (frame : Frame) (factor : Factor) : Species frame → Nat
  | .old species => match factor with
      | .old actor => CPS1InitiationTermination.Accounting.actorCount actor species
      | _ => 0
  | .abce1 _ | .boundSmall _ _ => if factor = .abce1 then 1 else 0
  | .preSplit _ _ => if factor = .abce1 ∨ factor = .old .eRF1 then 1 else 0
  | .eIF3j => if factor = .eIF3j then 1 else 0
  | .smallWithMessage _ => if factor = .abce1 ∨ factor = .old .eIF1 ∨
      factor = .old .eIF1A ∨ factor = .old .eIF3 then 1 else 0
  | .primedSmall _ => if factor = .abce1 ∨ factor = .old .eIF1 ∨
      factor = .old .eIF1A ∨ factor = .old .eIF3 ∨ factor = .eIF3j then 1 else 0
  | .next43 _ => if factor = .abce1 ∨ factor = .old .eIF1 ∨ factor = .old .eIF1A ∨
      factor = .old .eIF3 ∨ factor = .eIF3j ∨ factor = .old .eIF2 then 1 else 0
  | _ => 0

def residueCount (frame : Frame) (aa : AA) : Species frame → Nat
  | .old species => CPS1ResourceExecution.residueCount aa species
  | .next43 _ => if AA.M = aa then 1 else 0
  | _ => 0

def messageCount (frame : Frame) : Species frame → Nat
  | .old (.postTerminationInitiator) | .old (.postTerminationElongator _) => 1
  | .preSplit _ _ | .boundSmall _ _ | .smallWithMessage _ | .messageCoordinate => 1
  | _ => 0

def initiatorCount (frame : Frame) : Species frame → Nat
  | .old species => CPS1InitiationTermination.Accounting.initiatorCount species
  | .preSplit .initiator _ | .boundSmall .initiator _ | .next43 _ => 1
  | _ => 0

theorem primitive_actor_balance (frame : Frame) (primitive : Primitive) (factor : Factor) :
    moiety frame (actorCount frame factor) (primitive.reactants frame) =
      moiety frame (actorCount frame factor) (primitive.products frame) := by
  cases factor with
  | abce1 =>
      cases primitive <;> simp [moiety,Primitive.reactants,Primitive.products,Reaction.reactants,Reaction.products,actorCount,
        postSpecies,returnedTrna]
  | eIF3j =>
      cases primitive <;> simp [moiety,Primitive.reactants,Primitive.products,Reaction.reactants,Reaction.products,actorCount,
        postSpecies,returnedTrna]
  | old actor =>
      cases actor <;> cases primitive <;>
        simp [moiety,Primitive.reactants,Primitive.products,Reaction.reactants,Reaction.products,actorCount,
          CPS1InitiationTermination.Accounting.actorCount,postSpecies,returnedTrna]
      all_goals cases ‹Trna› <;> rfl

theorem primitive_residue_message_balance (frame : Frame) (primitive : Primitive) (aa : AA) :
    moiety frame (residueCount frame aa) (primitive.reactants frame) =
      moiety frame (residueCount frame aa) (primitive.products frame) ∧
    moiety frame (messageCount frame) (primitive.reactants frame) =
      moiety frame (messageCount frame) (primitive.products frame) ∧
    moiety frame (initiatorCount frame) (primitive.reactants frame) =
      moiety frame (initiatorCount frame) (primitive.products frame) := by
  cases primitive <;>
    simp [moiety,Primitive.reactants,Primitive.products,Reaction.reactants,Reaction.products,residueCount,messageCount,initiatorCount,
      CPS1ResourceExecution.residueCount,CPS1InitiationTermination.Accounting.initiatorCount,
      postSpecies,returnedTrna]
  all_goals cases ‹Trna›
  all_goals dsimp (config := {failIfUnchanged := false}) [postSpecies,returnedTrna,
    CPS1ResourceExecution.residueCount,CPS1InitiationTermination.Accounting.initiatorCount]
  all_goals trivial

/-- The next small-subunit state retains ABCE1 with the human observed ATP/ADP hybrid. -/
def siteResolvedContinuation (frame : Frame) : List Primitive :=
  [.engageControl (sourceTrna frame),.engageWork (sourceTrna frame),
    .splitHydrolyzingFirst (sourceTrna frame),.removeTrna (sourceTrna frame) humanHybrid,
    .removeMessage humanHybrid,.chargeNextInitiator,.captureNext humanHybrid]

theorem source_post_restriction (frame : Frame) :
    postSpecies (sourceTrna frame) = frame.postSpecies := by
  rcases frame with ⟨message,peptide,program,native⟩
  rcases peptide with ⟨head,tail⟩
  cases tail <;> rfl


end CPS1Recycling
