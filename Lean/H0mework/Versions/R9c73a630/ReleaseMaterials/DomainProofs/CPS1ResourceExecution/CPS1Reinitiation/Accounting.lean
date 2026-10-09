import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Reinitiation.Program

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1Reinitiation.Accounting
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

inductive Currency | adenylate | guanylate | phosphate

def currencyCount (frame : CPS1Recycling.Frame) : Currency → Species frame → Nat
  | .adenylate, .retained species => CPS1Recycling.adenylate frame species
  | .adenylate, .adp => 1
  | .adenylate, .scanning sites _ _ | .adenylate, .recognized sites _ _
  | .adenylate, .committed sites _ _ =>
      CPS1Recycling.siteMeasure CPS1Recycling.nucleotideAdenylate sites
  | .guanylate, .retained species => CPS1Recycling.guanylate frame species
  | .guanylate, .scanning _ _ _ | .guanylate, .recognized _ _ _
  | .guanylate, .committed _ _ _ => 1
  | .phosphate, .retained species => CPS1Recycling.phosphate frame species
  | .phosphate, .adp => 2
  | .phosphate, .scanning sites _ _ | .phosphate, .recognized sites _ _ =>
      CPS1Recycling.siteMeasure CPS1Recycling.nucleotidePhosphate sites + 3
  | .phosphate, .committed sites _ _ =>
      CPS1Recycling.siteMeasure CPS1Recycling.nucleotidePhosphate sites + 2
  | _, _ => 0

def retainedSites (frame : CPS1Recycling.Frame) : CPS1Recycling.Species frame →
    Option CPS1Recycling.Sites
  | .abce1 sites | .preSplit _ sites | .boundSmall _ sites
  | .smallWithMessage sites | .primedSmall sites | .next43 sites => some sites
  | _ => none

/-- Arbitrary joint-site readouts preserve occupancy and the two-site correlation. -/
def sitesCount (frame : CPS1Recycling.Frame) (read : CPS1Recycling.Sites → Nat) :
    Species frame → Nat
  | .retained species => ((retainedSites frame species).map read).getD 0
  | .scanning sites _ _ | .recognized sites _ _ | .committed sites _ _ => read sites
  | _ => 0

def trnaCount (frame : CPS1Recycling.Frame) : Species frame → Nat
  | .retained species => CPS1Recycling.trnaCount frame species
  | .scanning _ _ _ | .recognized _ _ _ | .committed _ _ _ => 1
  | _ => 0

def oldTrnaRoleCount (role : CPS1Recycling.Trna) : CPS1ResourceExecution.Species → Nat :=
  match role with
  | .initiator => CPS1InitiationTermination.Accounting.initiatorCount
  | .elongator aa => fun species => match species with
      | .tRNA other | .aaTRNA other | .postTerminationElongator other => if other = aa then 1 else 0
      | .peptidyl chain | .preTranslocation chain | .terminatingPeptidyl chain =>
          if chain.last = aa then 1 else 0
      | .aSite chain other =>
          (if chain.last = aa then 1 else 0) + (if other = aa then 1 else 0)
      | .initiatorASite other | .initiatorPreTranslocation other => if other = aa then 1 else 0
      | _ => 0

def retainedTrnaRoleCount (frame : CPS1Recycling.Frame) (role : CPS1Recycling.Trna) :
    CPS1Recycling.Species frame → Nat
  | .old species => oldTrnaRoleCount role species
  | .preSplit other _ | .boundSmall other _ => if other = role then 1 else 0
  | .next43 _ => if role = .initiator then 1 else 0
  | _ => 0

def trnaRoleCount (frame : CPS1Recycling.Frame) (role : CPS1Recycling.Trna) : Species frame → Nat
  | .retained species => retainedTrnaRoleCount frame role species
  | .scanning _ _ _ | .recognized _ _ _ | .committed _ _ _ => if role = .initiator then 1 else 0
  | _ => 0

def subunitCount (frame : CPS1Recycling.Frame) :
    CPS1InitiationTermination.Accounting.Subunit → Species frame → Nat
  | .small, .retained species => CPS1Recycling.smallCount frame species
  | .large, .retained species => CPS1Recycling.largeCount frame species
  | .small, .scanning _ _ _ | .small, .recognized _ _ _ | .small, .committed _ _ _ => 1
  | _, _ => 0

def oldFactorCount (frame : CPS1Recycling.Frame) (factor : CPS1Recycling.Factor) :
    Species frame → Nat
  | .retained species => CPS1Recycling.actorCount frame factor species
  | .scanning _ _ _ => match factor with
      | .old actor => if actor = .eIF1 ∨ actor = .eIF1A ∨ actor = .eIF2 ∨ actor = .eIF3 then 1 else 0
      | .abce1 => 1
      | .eIF3j => 0
  | .recognized _ _ _ | .committed _ _ _ => match factor with
      | .old actor => if actor = .eIF1A ∨ actor = .eIF2 ∨ actor = .eIF3 ∨ actor = .eIF5 then 1 else 0
      | .abce1 => 1
      | .eIF3j => 0
  | _ => 0

def recruitmentFactorCount (frame : CPS1Recycling.Frame) (factor : RecruitmentFactor) :
    Species frame → Nat
  | .factor other => if other = factor then 1 else 0
  | .scanning _ _ _ | .recognized _ _ _ | .committed _ _ _ => 1
  | _ => 0

/-- A recognition guard carries no molecule; the material RNA stays in its compound. -/
def rnaCount (frame : CPS1Recycling.Frame) (read : RegisteredRna → Nat) : Species frame → Nat
  | .rna rna | .scanning _ rna _ | .recognized _ rna _ | .committed _ rna _ => read rna
  | _ => 0

def residueCount (frame : CPS1Recycling.Frame) (aa : AA) : Species frame → Nat
  | .retained species => CPS1Recycling.residueCount frame aa species
  | .scanning _ _ _ | .recognized _ _ _ | .committed _ _ _ => if AA.M = aa then 1 else 0
  | _ => 0

def oldMessageCount (frame : CPS1Recycling.Frame) : Species frame → Nat
  | .retained species => CPS1Recycling.messageCount frame species
  | _ => 0

/-- The arbitrary readouts include exact RNA identity, all RNA chemistry in the
registered word, ABCE1 count, and every joint or individual site occupancy. -/
inductive ConservedMeasure
  | currency (currency : Currency)
  | abce1Sites (read : CPS1Recycling.Sites → Nat)
  | trna
  | trnaRole (role : CPS1Recycling.Trna)
  | subunit (subunit : CPS1InitiationTermination.Accounting.Subunit)
  | oldFactor (factor : CPS1Recycling.Factor)
  | recruitmentFactor (factor : RecruitmentFactor)
  | rna (read : RegisteredRna → Nat)
  | residue (aa : AA)
  | oldMessage

def measure (frame : CPS1Recycling.Frame) : ConservedMeasure → Species frame → Nat
  | .currency currency => currencyCount frame currency
  | .abce1Sites read => sitesCount frame read
  | .trna => trnaCount frame
  | .trnaRole role => trnaRoleCount frame role
  | .subunit subunit => subunitCount frame subunit
  | .oldFactor factor => oldFactorCount frame factor
  | .recruitmentFactor factor => recruitmentFactorCount frame factor
  | .rna read => rnaCount frame read
  | .residue aa => residueCount frame aa
  | .oldMessage => oldMessageCount frame

def total (frame : CPS1Recycling.Frame) (channel : ConservedMeasure) (stock : Stock frame) : Nat :=
  (stock.map (measure frame channel)).sum

theorem primitive_conservation (frame : CPS1Recycling.Frame) (primitive : Primitive)
    (channel : ConservedMeasure) :
    total frame channel (primitive.reactants frame) = total frame channel (primitive.products frame) := by
  cases channel with
  | currency currency =>
      cases currency <;> cases primitive <;>
        simp [total,measure,currencyCount,Primitive.reactants,Primitive.products,
          CPS1Recycling.adenylate,CPS1Recycling.guanylate,CPS1Recycling.phosphate,
          CPS1ResourceExecution.adenylate,CPS1ResourceExecution.guanylate,phosphateGroups]
      all_goals split <;> simp_all [currencyCount]
  | abce1Sites read =>
      cases primitive <;> simp [total,measure,sitesCount,retainedSites,Primitive.reactants,Primitive.products]
      all_goals split <;> simp_all [sitesCount]
  | trna =>
      cases primitive <;> simp [total,measure,trnaCount,Primitive.reactants,Primitive.products,
        CPS1Recycling.trnaCount,CPS1ResourceExecution.trnaCount]
      all_goals split <;> simp_all [trnaCount]
  | trnaRole role =>
      cases role <;> cases primitive <;>
        simp [total,measure,trnaRoleCount,retainedTrnaRoleCount,oldTrnaRoleCount,
          CPS1InitiationTermination.Accounting.initiatorCount,Primitive.reactants,Primitive.products]
      all_goals split <;> simp_all [trnaRoleCount]
  | subunit subunit =>
      cases subunit <;> cases primitive <;>
        simp [total,measure,subunitCount,Primitive.reactants,Primitive.products,
          CPS1Recycling.smallCount,CPS1Recycling.largeCount,CPS1InitiationTermination.Accounting.subunitCount]
      all_goals split <;> simp_all [subunitCount]
  | oldFactor factor =>
      cases factor with
      | old actor =>
          cases actor <;> cases primitive <;>
            simp [total,measure,oldFactorCount,Primitive.reactants,Primitive.products,
              CPS1Recycling.actorCount,CPS1InitiationTermination.Accounting.actorCount]
          all_goals split <;> simp_all [oldFactorCount]
      | abce1 =>
          cases primitive <;> simp [total,measure,oldFactorCount,Primitive.reactants,Primitive.products,
            CPS1Recycling.actorCount]
          all_goals split <;> simp_all [oldFactorCount]
      | eIF3j =>
          cases primitive <;> simp [total,measure,oldFactorCount,Primitive.reactants,Primitive.products,
            CPS1Recycling.actorCount]
          all_goals split <;> simp_all [oldFactorCount]
  | recruitmentFactor factor =>
      cases factor <;> cases primitive <;>
        simp [total,measure,recruitmentFactorCount,Primitive.reactants,Primitive.products]
      all_goals split <;> simp_all [recruitmentFactorCount]
  | rna read =>
      cases primitive <;> simp [total,measure,rnaCount,Primitive.reactants,Primitive.products]
      all_goals split <;> simp_all [rnaCount]
  | residue aa =>
      cases primitive <;> simp [total,measure,residueCount,Primitive.reactants,Primitive.products,
        CPS1Recycling.residueCount,CPS1ResourceExecution.residueCount]
      all_goals split <;> simp_all [residueCount]
  | oldMessage =>
      cases primitive <;> simp [total,measure,oldMessageCount,Primitive.reactants,Primitive.products,
        CPS1Recycling.messageCount]
      all_goals split <;> simp_all [oldMessageCount]

theorem execution_conservation (frame : CPS1Recycling.Frame) (program : List Primitive)
    (stock : Stock frame) (channel : ConservedMeasure) :
    total frame channel stock =
      total frame channel (Inventory.execute (Primitive.reactants frame) (Primitive.products frame)
        program stock).stock :=
  Inventory.execution_measure_preserved _ _ _ _ _
    (fun primitive _ => primitive_conservation frame primitive channel)

end CPS1Reinitiation.Accounting
