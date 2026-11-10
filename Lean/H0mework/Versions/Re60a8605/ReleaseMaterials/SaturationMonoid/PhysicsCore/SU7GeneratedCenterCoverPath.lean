import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.SU7GeneratedCurrentSourceClosure
import H0mework.Realization.Observation.RewriteSystem

/-!
# Generated endpoint repairs as A6 center-cover paths

The finite raw-code successor law already produces generated endpoint pairs
whose residual energy drops by one.  This module identifies the exact native
representation-side content of such a step without importing a projection
core, P950 witness, thin datum, coverage theorem, normalizer, or final
compatibility certificate.

Every generated endpoint repair induces an existing
`SU7A6UnitCenterCoverDisplacement` between the endpoint/source labels.  This is
an honest type-level bridge, but not by itself a confluence theorem: the
repository already proves that unit center-cover algebra is permissive for
every signed-height unit descent.

Two finite models make the boundary exact:

* at fiber `n=3`, bound `3`, the generated endpoint repair relation is
  terminating and confluent, with unique terminal pair `(3,3)`;
* at fiber `n=5`, bound `7`, the active canonical source `(2,7)` has two
  generated zero-energy center-cover repairs `(3,7)` and `(5,5)`, so the full
  endpoint repair relation is not locally confluent.

Thus generated membership, active branch/incidence, unit residual descent,
and center-cover displacement still do not make path confluence automatic.
Global endpoint closure does, however, generate residual confluence: every
generated pair reaches some zero-residual terminal, without identifying
distinct terminal lineages.  Exact-state confluence still needs a path
selector/normal-form law or an equivalent critical-pair theorem; choosing the
residual quotient as the intended standing path remains a separate relevance
and transport obligation.
-/

namespace SaturationMonoid
namespace PhysicsCore
namespace SU7GeneratedCenterCoverPath

open Relation
open StandardModelConstraint
open SU7PreHolonomyCurrentSourceBoundary
open SU7GeneratedCurrentSourceClosure

noncomputable section

/-- One bounded, allowed, Boolean-atomic endpoint pair in the generated
no-prime room.  This is a property of raw endpoint operations, not a stored
certificate in physical state. -/
def GeneratedEndpointPair
    (n bound : Nat) (pair : Nat × Nat) : Prop :=
  generatedNoPrimeAllowedPredicate n bound pair.1 pair.2 = true ∧
    pair.1 ∈ rawCodeBoundedList bound ∧
      pair.2 ∈ rawCodeBoundedList bound ∧
        natMultiplicativelyAtomicCheck pair.1 = true ∧
          natMultiplicativelyAtomicCheck pair.2 = true

def endpointEnergy (n : Nat) (pair : Nat × Nat) : Nat :=
  rawCodePairResidualEnergy n pair.1 pair.2

/-- The existing A6 endpoint/source label for one raw generated pair. -/
def endpointSourceLabel (n : Nat) (pair : Nat × Nat) : SU7A6WeightLabel :=
  su7A6EndpointSourceLabel pair.1 pair.2 (endpointEnergy n pair)

@[simp] theorem endpointSourceLabel_signedHeight
    (n : Nat) (pair : Nat × Nat) :
    su7A6SignedHeight (endpointSourceLabel n pair) =
      (endpointEnergy n pair : Int) := by
  simp [endpointSourceLabel, endpointEnergy,
    su7A6EndpointSourceLabel_signedHeight]

/-- The complete generated endpoint repair relation: both endpoints survive
the finite generated filter, and raw residual energy drops by exactly one. -/
def GeneratedEndpointRepairStep
    (n bound : Nat) (source target : Nat × Nat) : Prop :=
  GeneratedEndpointPair n bound source ∧
    GeneratedEndpointPair n bound target ∧
      endpointEnergy n target + 1 = endpointEnergy n source

namespace GeneratedEndpointRepairStep

variable {n bound : Nat} {source target : Nat × Nat}

theorem source_generated
    (H : GeneratedEndpointRepairStep n bound source target) :
    GeneratedEndpointPair n bound source :=
  H.1

theorem target_generated
    (H : GeneratedEndpointRepairStep n bound source target) :
    GeneratedEndpointPair n bound target :=
  H.2.1

theorem energy_unit
    (H : GeneratedEndpointRepairStep n bound source target) :
    endpointEnergy n target + 1 = endpointEnergy n source :=
  H.2.2

/-- Every generated raw endpoint repair is an existing native A6
unit-center-cover displacement between the corresponding endpoint/source
labels.  The generated/filter premises select the target; the permissive
center-cover algebra then records its representation displacement. -/
def centerCoverMove
    (H : GeneratedEndpointRepairStep n bound source target) :
    SU7A6UnitCenterCoverDisplacement
      (endpointSourceLabel n source)
      (endpointSourceLabel n target) := by
  apply su7A6UnitCenterCoverDisplacement_of_signedHeight_unit
  rw [endpointSourceLabel_signedHeight, endpointSourceLabel_signedHeight]
  exact_mod_cast H.energy_unit

/-- Raw residual energy is a termination grade for every generated endpoint
repair relation. -/
theorem terminating (n bound : Nat) :
    Terminating (GeneratedEndpointRepairStep n bound) := by
  unfold Terminating
  exact
    (InvImage.wf (endpointEnergy n) wellFounded_lt).mono (by
      intro target source hstep
      change GeneratedEndpointRepairStep n bound source target at hstep
      change endpointEnergy n target < endpointEnergy n source
      have hunit := hstep.energy_unit
      omega)

end GeneratedEndpointRepairStep

theorem generatedEndpointPair_of_boundedAtomic
    {n bound left right : Nat}
    (hleft_mem : left ∈ rawCodeBoundedList bound)
    (hright_mem : right ∈ rawCodeBoundedList bound)
    (hleft_check : natMultiplicativelyAtomicCheck left = true)
    (hright_check : natMultiplicativelyAtomicCheck right = true) :
    GeneratedEndpointPair n bound (left, right) :=
  ⟨generatedNoPrimeAllowedPredicate_of_boundedAtomicRawCodePair
      hleft_mem hright_mem hleft_check hright_check,
    hleft_mem, hright_mem, hleft_check, hright_check⟩

/-! ## Residual confluence without lineage collapse -/

/-- Two endpoint states are equivalent at the residual layer when their
generated raw residual energies agree.  This relation deliberately does not
identify their endpoint pairs or lineages. -/
def EndpointResidualEquivalent
    (n : Nat) (left right : Nat × Nat) : Prop :=
  endpointEnergy n left = endpointEnergy n right

theorem endpointResidualEquivalent_refl
    (n : Nat) (pair : Nat × Nat) :
    EndpointResidualEquivalent n pair pair :=
  rfl

theorem endpointResidualEquivalent_symm
    {n : Nat} {left right : Nat × Nat}
    (H : EndpointResidualEquivalent n left right) :
    EndpointResidualEquivalent n right left :=
  H.symm

theorem endpointResidualEquivalent_trans
    {n : Nat} {left middle right : Nat × Nat}
    (Hleft : EndpointResidualEquivalent n left middle)
    (Hright : EndpointResidualEquivalent n middle right) :
    EndpointResidualEquivalent n left right :=
  Hleft.trans Hright

/-- Two generated endpoint paths are residual-joinable when each can be
extended to states with the same residual energy.  The terminal states need
not be equal. -/
def ResidualJoinable
    (n bound : Nat) (left right : Nat × Nat) : Prop :=
  ∃ leftTerminal rightTerminal : Nat × Nat,
    RewriteStar (GeneratedEndpointRepairStep n bound) left leftTerminal ∧
      RewriteStar (GeneratedEndpointRepairStep n bound) right rightTerminal ∧
        EndpointResidualEquivalent n leftTerminal rightTerminal

/-- Stronger global residual-cofinality statement on the generated room.  It
is defined from endpoint operations before any standing-audit vocabulary is
introduced. -/
def GeneratedEndpointResidualConfluent (n bound : Nat) : Prop :=
  ∀ left right : Nat × Nat,
    GeneratedEndpointPair n bound left →
      GeneratedEndpointPair n bound right →
        ResidualJoinable n bound left right

/-- Global generated endpoint closure sends every generated pair to some
zero-residual terminal.  The terminal endpoint identity is intentionally not
claimed unique. -/
theorem generatedEndpointPair_reaches_residualZero_of_closure
    {n bound : Nat}
    (Hclosure : GeneratedSourceClosure n bound)
    {pair : Nat × Nat}
    (Hpair : GeneratedEndpointPair n bound pair) :
    ∃ terminal : Nat × Nat,
      RewriteStar (GeneratedEndpointRepairStep n bound) pair terminal ∧
        GeneratedEndpointPair n bound terminal ∧
          endpointEnergy n terminal = 0 := by
  let P : Nat → Prop := fun energy =>
    ∀ pair : Nat × Nat,
      GeneratedEndpointPair n bound pair →
        endpointEnergy n pair = energy →
          ∃ terminal : Nat × Nat,
            RewriteStar
                (GeneratedEndpointRepairStep n bound) pair terminal ∧
              GeneratedEndpointPair n bound terminal ∧
                endpointEnergy n terminal = 0
  have hP : ∀ energy : Nat, P energy := by
    intro energy
    induction energy using Nat.strong_induction_on with
    | h energy ih =>
        intro source hsource hsourceEnergy
        by_cases hzero : energy = 0
        · exact
            ⟨source, ReflTransGen.refl, hsource,
              hsourceEnergy.trans hzero⟩
        · have hsourceNonzero : endpointEnergy n source ≠ 0 := by
            rw [hsourceEnergy]
            exact hzero
          rcases
              Hclosure source.1 source.2
                hsource.1 hsource.2.1 hsource.2.2.1
                hsource.2.2.2.1 hsource.2.2.2.2 hsourceNonzero with
            ⟨targetLeft, targetRight, htargetAllowed,
              htargetLeft, htargetRight, htargetLeftCheck,
              htargetRightCheck, hunit⟩
          let target : Nat × Nat := (targetLeft, targetRight)
          have htarget : GeneratedEndpointPair n bound target := by
            exact
              ⟨htargetAllowed, htargetLeft, htargetRight,
                htargetLeftCheck, htargetRightCheck⟩
          have hstep :
              GeneratedEndpointRepairStep n bound source target := by
            refine ⟨hsource, htarget, ?_⟩
            simpa [endpointEnergy, target] using hunit
          have htargetLt : endpointEnergy n target < energy := by
            have hstepUnit := hstep.energy_unit
            rw [hsourceEnergy] at hstepUnit
            omega
          rcases
              ih (endpointEnergy n target) htargetLt
                target htarget rfl with
            ⟨terminal, htargetTerminal, hterminalGenerated,
              hterminalZero⟩
          exact
            ⟨terminal,
              (ReflTransGen.single hstep).trans htargetTerminal,
              hterminalGenerated, hterminalZero⟩
  exact hP (endpointEnergy n pair) pair Hpair rfl

/-- Global successor closure is exactly strong enough for residual
confluence: all generated endpoint states can be extended to residual zero,
without forcing their terminal endpoint identities to coincide. -/
theorem generatedSourceClosure_residualConfluent
    {n bound : Nat}
    (Hclosure : GeneratedSourceClosure n bound) :
    GeneratedEndpointResidualConfluent n bound := by
  intro left right hleft hright
  rcases
      generatedEndpointPair_reaches_residualZero_of_closure
        Hclosure hleft with
    ⟨leftTerminal, hleftPath, _hleftGenerated, hleftZero⟩
  rcases
      generatedEndpointPair_reaches_residualZero_of_closure
        Hclosure hright with
    ⟨rightTerminal, hrightPath, _hrightGenerated, hrightZero⟩
  exact
    ⟨leftTerminal, rightTerminal, hleftPath, hrightPath,
      hleftZero.trans hrightZero.symm⟩

/-- Canonical active-branch/incidence lift of one generated endpoint pair. -/
def GeneratedEndpointPair.canonicalCell
    {n bound : Nat} {pair : Nat × Nat}
    (H : GeneratedEndpointPair n bound pair) :
    SU7BooleanAtomicRawBranchingCell n :=
  booleanAtomicCellOfRawCodePair n pair.1 pair.2 H.2.2.2.1 H.2.2.2.2

theorem GeneratedEndpointPair.canonicalCell_mem
    {n bound : Nat} {pair : Nat × Nat}
    (H : GeneratedEndpointPair n bound pair) :
    H.canonicalCell ∈
      gaugeFilteredBooleanAtomicRawBranchingCandidateList
        n bound (generatedNoPrimeAllowedPredicate n bound) := by
  exact booleanAtomicCellOfRawCodePair_mem_gaugeFiltered
    H.1 H.2.1 H.2.2.1 H.2.2.2.1 H.2.2.2.2

@[simp] theorem GeneratedEndpointPair.canonicalCell_branch
    {n bound : Nat} {pair : Nat × Nat}
    (H : GeneratedEndpointPair n bound pair) :
    H.canonicalCell.cell.branch = SU3FlagSchubertCell.e :=
  rfl

@[simp] theorem GeneratedEndpointPair.canonicalCell_incidence
    {n bound : Nat} {pair : Nat × Nat}
    (H : GeneratedEndpointPair n bound pair) :
    H.canonicalCell.cell.incidence =
      (.colorWeak : RunningSigmaBeta.SU7BlockIncidence) :=
  rfl

def repairPair
    {n : Nat} (repair : SU7BooleanAtomicRawBranchingCell n) : Nat × Nat :=
  (repair.cell.leftWeightCode, repair.cell.rightWeightCode)

/-- The current source step constructed by the 21-coordinate layer is exactly
a step of the generated endpoint repair relation. -/
theorem generatedCurrentSourceStep_to_endpointRepairStep
    {n sourceBound sourceEnergy : Nat}
    {D : SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy}
    {repair : SU7BooleanAtomicRawBranchingCell n}
    (H : GeneratedCurrentSourceStep D repair) :
    GeneratedEndpointRepairStep
      n sourceBound D.sourcePair (repairPair repair) := by
  have hsourceLeft :
      D.sourceCell.cell.leftWeightCode ∈ rawCodeBoundedList sourceBound :=
    booleanAtomicCell_left_mem_rawCodeBoundedList_of_mem_generated
      D.source_mem
  have hsourceRight :
      D.sourceCell.cell.rightWeightCode ∈ rawCodeBoundedList sourceBound :=
    booleanAtomicCell_right_mem_rawCodeBoundedList_of_mem_generated
      D.source_mem
  have hsource : GeneratedEndpointPair n sourceBound D.sourcePair := by
    simpa [SU7PreHolonomyCurrentSourceDatum.sourcePair] using
      (generatedEndpointPair_of_boundedAtomic
        hsourceLeft hsourceRight
        D.sourceCell.left_check D.sourceCell.right_check)
  have hrepairParts :
      repair ∈ booleanAtomicRawBranchingCandidateList n sourceBound ∧
        generatedNoPrimeAllowedPredicate n sourceBound
          repair.cell.leftWeightCode repair.cell.rightWeightCode = true := by
    simpa [gaugeFilteredBooleanAtomicRawBranchingCandidateList] using
      (List.mem_filter.mp H.1)
  have hrepairLeft :
      repair.cell.leftWeightCode ∈ rawCodeBoundedList sourceBound :=
    booleanAtomicCell_left_mem_rawCodeBoundedList_of_mem_generated
      hrepairParts.1
  have hrepairRight :
      repair.cell.rightWeightCode ∈ rawCodeBoundedList sourceBound :=
    booleanAtomicCell_right_mem_rawCodeBoundedList_of_mem_generated
      hrepairParts.1
  have hrepair :
      GeneratedEndpointPair n sourceBound (repairPair repair) := by
    simpa [repairPair] using
      (generatedEndpointPair_of_boundedAtomic
        hrepairLeft hrepairRight repair.left_check repair.right_check)
  refine ⟨hsource, hrepair, ?_⟩
  calc
    endpointEnergy n (repairPair repair) + 1 =
        rawAtomCodeBranchingDecompositionResidualEnergy repair.cell + 1 := by
      simp [endpointEnergy, repairPair,
        rawBranchingResidualEnergy_eq_codePair]
    _ = sourceEnergy := H.2.2.2
    _ = endpointEnergy n D.sourcePair := by
      simpa [endpointEnergy] using D.sourcePair_energy.symm

/-- Current active repair steps therefore carry a generated native
center-cover displacement without adding a new premise. -/
def generatedCurrentSourceStep_centerCoverMove
    {n sourceBound sourceEnergy : Nat}
    {D : SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy}
    {repair : SU7BooleanAtomicRawBranchingCell n}
    (H : GeneratedCurrentSourceStep D repair) :
    SU7A6UnitCenterCoverDisplacement
      (endpointSourceLabel n D.sourcePair)
      (endpointSourceLabel n (repairPair repair)) :=
  (generatedCurrentSourceStep_to_endpointRepairStep H).centerCoverMove

/-- Typed step used by downstream physical admissibility: the same generated
current repair step also carries its native center-cover path. -/
structure GeneratedCurrentSourceCenterCoverStep
    {n sourceBound sourceEnergy : Nat}
    (D : SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy)
    (repair : SU7BooleanAtomicRawBranchingCell n) where
  generated_step : GeneratedCurrentSourceStep D repair
  center_cover_move :
    SU7A6UnitCenterCoverDisplacement
      (endpointSourceLabel n D.sourcePair)
      (endpointSourceLabel n (repairPair repair))

def generatedCurrentSourceCenterCoverStep_of_step
    {n sourceBound sourceEnergy : Nat}
    {D : SU7PreHolonomyCurrentSourceDatum n sourceBound sourceEnergy}
    {repair : SU7BooleanAtomicRawBranchingCell n}
    (H : GeneratedCurrentSourceStep D repair) :
    GeneratedCurrentSourceCenterCoverStep D repair where
  generated_step := H
  center_cover_move := generatedCurrentSourceStep_centerCoverMove H

/-! ## The globally closed `n=3`, bound-three path is confluent -/

theorem pair_three_three_two_two :
    GeneratedEndpointPair 3 3 (2, 2) :=
  generatedEndpointPair_of_boundedAtomic
    (by norm_num [rawCodeBoundedList])
    (by norm_num [rawCodeBoundedList])
    natMultiplicativelyAtomicCheck_two
    natMultiplicativelyAtomicCheck_two

theorem pair_three_three_two_three :
    GeneratedEndpointPair 3 3 (2, 3) :=
  generatedEndpointPair_of_boundedAtomic
    (by norm_num [rawCodeBoundedList])
    (by norm_num [rawCodeBoundedList])
    natMultiplicativelyAtomicCheck_two
    natMultiplicativelyAtomicCheck_three

theorem pair_three_three_three_two :
    GeneratedEndpointPair 3 3 (3, 2) :=
  generatedEndpointPair_of_boundedAtomic
    (by norm_num [rawCodeBoundedList])
    (by norm_num [rawCodeBoundedList])
    natMultiplicativelyAtomicCheck_three
    natMultiplicativelyAtomicCheck_two

theorem pair_three_three_three_three :
    GeneratedEndpointPair 3 3 (3, 3) :=
  generatedEndpointPair_of_boundedAtomic
    (by norm_num [rawCodeBoundedList])
    (by norm_num [rawCodeBoundedList])
    natMultiplicativelyAtomicCheck_three
    natMultiplicativelyAtomicCheck_three

theorem step_three_three_two_two_to_two_three :
    GeneratedEndpointRepairStep 3 3 (2, 2) (2, 3) :=
  ⟨pair_three_three_two_two, pair_three_three_two_three, by
    norm_num [endpointEnergy, rawCodePairResidualEnergy,
      rawCodePairResidual]⟩

theorem step_three_three_two_three_to_three_three :
    GeneratedEndpointRepairStep 3 3 (2, 3) (3, 3) :=
  ⟨pair_three_three_two_three, pair_three_three_three_three, by
    norm_num [endpointEnergy, rawCodePairResidualEnergy,
      rawCodePairResidual]⟩

theorem step_three_three_three_two_to_three_three :
    GeneratedEndpointRepairStep 3 3 (3, 2) (3, 3) :=
  ⟨pair_three_three_three_two, pair_three_three_three_three, by
    norm_num [endpointEnergy, rawCodePairResidualEnergy,
      rawCodePairResidual]⟩

theorem generatedEndpointPair_three_three_cases
    {pair : Nat × Nat}
    (H : GeneratedEndpointPair 3 3 pair) :
    pair = (2, 2) ∨ pair = (2, 3) ∨
      pair = (3, 2) ∨ pair = (3, 3) := by
  rcases pair with ⟨left, right⟩
  rcases atomic_endpoint_cases_bound_three H.2.1 H.2.2.2.1 with
    rfl | rfl <;>
    rcases atomic_endpoint_cases_bound_three H.2.2.1 H.2.2.2.2 with
      rfl | rfl <;> simp

theorem generatedEndpointPair_three_three_reaches_terminal
    {pair : Nat × Nat}
    (H : GeneratedEndpointPair 3 3 pair) :
    RewriteStar (GeneratedEndpointRepairStep 3 3) pair (3, 3) := by
  rcases generatedEndpointPair_three_three_cases H with
    rfl | rfl | rfl | rfl
  · exact
      (ReflTransGen.single step_three_three_two_two_to_two_three).trans
        (ReflTransGen.single step_three_three_two_three_to_three_three)
  · exact ReflTransGen.single step_three_three_two_three_to_three_three
  · exact ReflTransGen.single step_three_three_three_two_to_three_three
  · exact ReflTransGen.refl

theorem generatedEndpointRepairStep_three_three_locallyConfluent :
    LocallyConfluent (GeneratedEndpointRepairStep 3 3) := by
  intro _source left right hleft hright
  exact
    ⟨(3, 3),
      generatedEndpointPair_three_three_reaches_terminal
        hleft.target_generated,
      generatedEndpointPair_three_three_reaches_terminal
        hright.target_generated⟩

/-- The nontrivial positive closure model has genuine finite path
confluence, not merely successor existence. -/
theorem generatedEndpointRepairStep_three_three_confluent :
    Confluent (GeneratedEndpointRepairStep 3 3) :=
  newman
    (GeneratedEndpointRepairStep.terminating 3 3)
    generatedEndpointRepairStep_three_three_locallyConfluent

/-! ## Center-cover/unit descent still does not force confluence -/

theorem pair_five_seven_two_seven :
    GeneratedEndpointPair 5 7 (2, 7) :=
  generatedEndpointPair_of_boundedAtomic
    (by norm_num [rawCodeBoundedList])
    (by norm_num [rawCodeBoundedList])
    natMultiplicativelyAtomicCheck_two
    natMultiplicativelyAtomicCheck_seven

theorem pair_five_seven_three_seven :
    GeneratedEndpointPair 5 7 (3, 7) :=
  generatedEndpointPair_of_boundedAtomic
    (by norm_num [rawCodeBoundedList])
    (by norm_num [rawCodeBoundedList])
    natMultiplicativelyAtomicCheck_three
    natMultiplicativelyAtomicCheck_seven

theorem pair_five_seven_five_five :
    GeneratedEndpointPair 5 7 (5, 5) :=
  generatedEndpointPair_of_boundedAtomic
    (by norm_num [rawCodeBoundedList])
    (by norm_num [rawCodeBoundedList])
    natMultiplicativelyAtomicCheck_five
    natMultiplicativelyAtomicCheck_five

theorem step_five_seven_two_seven_to_three_seven :
    GeneratedEndpointRepairStep 5 7 (2, 7) (3, 7) :=
  ⟨pair_five_seven_two_seven, pair_five_seven_three_seven, by
    norm_num [endpointEnergy, rawCodePairResidualEnergy,
      rawCodePairResidual]⟩

theorem step_five_seven_two_seven_to_five_five :
    GeneratedEndpointRepairStep 5 7 (2, 7) (5, 5) :=
  ⟨pair_five_seven_two_seven, pair_five_seven_five_five, by
    norm_num [endpointEnergy, rawCodePairResidualEnergy,
      rawCodePairResidual]⟩

theorem rewriteStar_eq_of_no_outgoing
    {State : Type*} {step : State → State → Prop}
    {source target : State}
    (hno : ∀ next : State, ¬ step source next)
    (H : RewriteStar step source target) :
    source = target := by
  induction H with
  | refl => rfl
  | tail _ hstep ih =>
      subst_vars
      exact (hno _ hstep).elim

theorem no_outgoing_of_endpointEnergy_zero
    {n bound : Nat} {source : Nat × Nat}
    (hzero : endpointEnergy n source = 0) :
    ∀ target : Nat × Nat,
      ¬ GeneratedEndpointRepairStep n bound source target := by
  intro target hstep
  have hunit := hstep.energy_unit
  rw [hzero] at hunit
  omega

theorem pair_five_seven_three_seven_energy_zero :
    endpointEnergy 5 (3, 7) = 0 := by
  norm_num [endpointEnergy, rawCodePairResidualEnergy, rawCodePairResidual]

theorem pair_five_seven_five_five_energy_zero :
    endpointEnergy 5 (5, 5) = 0 := by
  norm_num [endpointEnergy, rawCodePairResidualEnergy, rawCodePairResidual]

/-- The two terminal descendants remain different endpoint lineages while
being exactly equal at the residual layer. -/
theorem five_seven_zero_pairs_distinct_but_residualEquivalent :
    (3, 7) ≠ (5, 5) ∧
      EndpointResidualEquivalent 5 (3, 7) (5, 5) := by
  constructor
  · norm_num
  · exact
      pair_five_seven_three_seven_energy_zero.trans
        pair_five_seven_five_five_energy_zero.symm

theorem five_seven_zero_fork_residualJoinable :
    ResidualJoinable 5 7 (3, 7) (5, 5) :=
  ⟨(3, 7), (5, 5), ReflTransGen.refl, ReflTransGen.refl,
    five_seven_zero_pairs_distinct_but_residualEquivalent.2⟩

/-- Even with canonical active branch/incidence lifts and native center-cover
moves on both legs, scalar unit descent has a nonjoinable endpoint fork. -/
theorem generatedEndpointRepairStep_five_seven_not_locallyConfluent :
    ¬ LocallyConfluent (GeneratedEndpointRepairStep 5 7) := by
  intro hlocal
  rcases
      hlocal (2, 7) (3, 7) (5, 5)
        step_five_seven_two_seven_to_three_seven
        step_five_seven_two_seven_to_five_five with
    ⟨join, hleft, hright⟩
  have hleftEq : (3, 7) = join :=
    rewriteStar_eq_of_no_outgoing
      (no_outgoing_of_endpointEnergy_zero
        pair_five_seven_three_seven_energy_zero)
      hleft
  have hrightEq : (5, 5) = join :=
    rewriteStar_eq_of_no_outgoing
      (no_outgoing_of_endpointEnergy_zero
        pair_five_seven_five_five_energy_zero)
      hright
  have : (3, 7) = (5, 5) := hleftEq.trans hrightEq.symm
  norm_num at this

theorem generatedEndpointRepairStep_five_seven_not_confluent :
    ¬ Confluent (GeneratedEndpointRepairStep 5 7) := by
  intro hconfluent
  apply generatedEndpointRepairStep_five_seven_not_locallyConfluent
  intro source left right hleft hright
  exact
    hconfluent source left right
      (ReflTransGen.single hleft) (ReflTransGen.single hright)

def five_seven_fork_steps_are_centerCover :
    SU7A6UnitCenterCoverDisplacement
        (endpointSourceLabel 5 (2, 7))
        (endpointSourceLabel 5 (3, 7)) ×
      SU7A6UnitCenterCoverDisplacement
        (endpointSourceLabel 5 (2, 7))
        (endpointSourceLabel 5 (5, 5)) :=
  ⟨step_five_seven_two_seven_to_three_seven.centerCoverMove,
    step_five_seven_two_seven_to_five_five.centerCoverMove⟩

end
end SU7GeneratedCenterCoverPath
end PhysicsCore
end SaturationMonoid
