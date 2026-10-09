import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Lean.Elab.Tactic.Omega
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deamination.Chemistry

set_option autoImplicit false

namespace CPS1ResourceExecution

inductive AA | A | C | D | E | F | G | H | I | K | L | M | N | P | Q | R | S | T | V | W | Y
  deriving DecidableEq, Repr

abbrev Peptide := AA × List AA

namespace Peptide
def word (p : Peptide) : List AA := p.1 :: p.2
def extend (p : Peptide) (a : AA) : Peptide := (p.1, p.2 ++ [a])
def last (p : Peptide) : AA := p.word.getLast (by simp [word])
end Peptide

inductive Actor
  | metRS | eIF1 | eIF1A | eIF2 | eIF3 | eIF5 | eIF5B | eRF1 | eRF3
  deriving DecidableEq, Repr

/-- The tRNA bound to a nascent chain is determined by its final residue.
The A-site complex retains both tRNAs until peptidyl transfer. -/
inductive Species
  | freeAA (a : AA) | tRNA (a : AA) | aaTRNA (a : AA)
  | peptidyl (p : Peptide) | aSite (p : Peptide) (a : AA)
  | preTranslocation (p : Peptide)
  | atp | amp | ppi | gtp | gdp | phosphate | water | proton
  | dna (word : List CPS1Deamination.Base) | ammonia
  | actor (factor : Actor) | initiatorTRNA | chargedInitiator | initiator48S | initiatorPSite
  | initiatorASite (a : AA) | initiatorPreTranslocation (a : AA)
  | subunit40 | subunit60 | ribosome80
  | terminatingInitiator | terminatingPeptidyl (p : Peptide)
  | releasedPeptide (p : Peptide) | postTerminationInitiator | postTerminationElongator (a : AA)
  deriving DecidableEq, Repr

/-- Source-program reactions retain every paid intermediate. Initiation and
termination are post-start-recognition actions; scanning/recycling keep their own input traces. -/
inductive Reaction
  | charge (a : AA)
  | deliver (p : Peptide) (a : AA)
  | transfer (p : Peptide) (a : AA)
  | translocate (p : Peptide)
  | hydrolyzePPi
  | deaminate (left right : List CPS1Deamination.Base)
  | chargeInitiator | captureInitiator | joinSubunit
  | deliverInitiator (a : AA) | transferInitiator (a : AA) | translocateInitiator (a : AA)
  | stopInitiator | stopPeptidyl (p : Peptide) | releaseInitiator | releasePeptidyl (p : Peptide)
  deriving DecidableEq, Repr

def factorStock (actors : List Actor) : List Species := actors.map Species.actor

namespace Reaction
def reactants : Reaction → List Species
  | .charge a => [.freeAA a, .tRNA a, .atp]
  | .deliver p a => [.peptidyl p, .aaTRNA a, .gtp, .water]
  | .transfer p a => [.aSite p a]
  | .translocate p => [.preTranslocation p, .gtp, .water]
  | .hydrolyzePPi => [.ppi, .water]
  | .deaminate left right => [.dna (left ++ CPS1Deamination.Base.A :: right), .water]
  | .chargeInitiator => [.freeAA .M, .initiatorTRNA, .atp, .actor .metRS]
  | .captureInitiator => [.chargedInitiator, .subunit40, .gtp, .water] ++
      factorStock [.eIF1, .eIF1A, .eIF2, .eIF3, .eIF5]
  | .joinSubunit => [.initiator48S, .subunit60, .gtp, .water, .actor .eIF1A, .actor .eIF5B]
  | .deliverInitiator a => [.initiatorPSite, .aaTRNA a, .gtp, .water]
  | .transferInitiator a => [.initiatorASite a]
  | .translocateInitiator a => [.initiatorPreTranslocation a, .gtp, .water]
  | .stopInitiator => [.initiatorPSite, .ribosome80, .gtp, .water, .actor .eRF1, .actor .eRF3]
  | .stopPeptidyl p => [.peptidyl p, .ribosome80, .gtp, .water, .actor .eRF1, .actor .eRF3]
  | .releaseInitiator => [.terminatingInitiator, .water]
  | .releasePeptidyl p => [.terminatingPeptidyl p, .water]

def products : Reaction → List Species
  | .charge a => [.aaTRNA a, .amp, .ppi]
  | .deliver p a => [.aSite p a, .gdp, .phosphate, .proton]
  | .transfer p a => [.preTranslocation (p.extend a), .tRNA p.last]
  | .translocate p => [.peptidyl p, .gdp, .phosphate, .proton]
  | .hydrolyzePPi => [.phosphate, .phosphate]
  | .deaminate left right => [.dna (left ++ CPS1Deamination.Base.I :: right), .ammonia]
  | .chargeInitiator => [.chargedInitiator, .amp, .ppi, .actor .metRS]
  | .captureInitiator => [.initiator48S, .gdp, .phosphate, .proton] ++
      factorStock [.eIF1, .eIF1A, .eIF2, .eIF3, .eIF5]
  | .joinSubunit => [.initiatorPSite, .ribosome80, .gdp, .phosphate, .proton, .actor .eIF1A, .actor .eIF5B]
  | .deliverInitiator a => [.initiatorASite a, .gdp, .phosphate, .proton]
  | .transferInitiator a => [.initiatorPreTranslocation a]
  | .translocateInitiator a => [.peptidyl (.M,[a]), .initiatorTRNA, .gdp, .phosphate, .proton]
  | .stopInitiator => [.terminatingInitiator, .gdp, .phosphate, .proton, .actor .eRF3]
  | .stopPeptidyl p => [.terminatingPeptidyl p, .gdp, .phosphate, .proton, .actor .eRF3]
  | .releaseInitiator => [.releasedPeptide (.M,[]), .postTerminationInitiator]
  | .releasePeptidyl p => [.releasedPeptide p, .postTerminationElongator p.last]

end Reaction

def speciesValue (μ : Species → ℚ) (stock : List Species) : ℚ :=
  (stock.map μ).sum

def adenylate : Species → Nat
  | .atp | .amp => 1 | _ => 0

def guanylate : Species → Nat
  | .gtp | .gdp => 1 | _ => 0

def phosphateGroups : Species → Nat
  | .atp | .gtp => 3 | .gdp | .ppi => 2
  | .amp | .phosphate => 1 | _ => 0

def trnaCount : Species → Nat
  | .tRNA _ | .aaTRNA _ | .peptidyl _ | .preTranslocation _ => 1
  | .aSite _ _ | .initiatorASite _ | .initiatorPreTranslocation _ => 2
  | .initiatorTRNA | .chargedInitiator | .initiator48S | .initiatorPSite
  | .terminatingInitiator | .terminatingPeptidyl _
  | .postTerminationInitiator | .postTerminationElongator _ => 1
  | _ => 0

def residueCount (a : AA) : Species → Nat
  | .freeAA b | .aaTRNA b => if b = a then 1 else 0
  | .peptidyl p | .preTranslocation p => p.word.count a
  | .aSite p b => p.word.count a + if b = a then 1 else 0
  | .chargedInitiator | .initiator48S | .initiatorPSite | .terminatingInitiator =>
      if AA.M = a then 1 else 0
  | .initiatorASite b | .initiatorPreTranslocation b =>
      (if AA.M = a then 1 else 0) + (if b = a then 1 else 0)
  | .terminatingPeptidyl p | .releasedPeptide p => p.word.count a
  | _ => 0

def moiety (v : Species → Nat) (stock : List Species) : Nat := (stock.map v).sum

theorem productive_moieties_preserved (r : Reaction) :
    moiety adenylate r.reactants = moiety adenylate r.products ∧
    moiety guanylate r.reactants = moiety guanylate r.products ∧
    moiety phosphateGroups r.reactants = moiety phosphateGroups r.products ∧
    moiety trnaCount r.reactants = moiety trnaCount r.products ∧
    (∀ a, moiety (residueCount a) r.reactants = moiety (residueCount a) r.products) := by
  cases r <;>
    simp [moiety, Reaction.reactants, Reaction.products, factorStock, adenylate, guanylate,
      phosphateGroups, trnaCount, residueCount, Peptide.word, Peptide.extend,
      List.count_cons, beq_iff_eq]
  all_goals
    intro a
    omega

end CPS1ResourceExecution
