import Mathlib.Algebra.Group.Nat.Even

/-!
# Atom projection defect core

Dependency-light theorem-design socket for the new research target:
representation/source repair demand is connected to multiplicative atom-pair
realization through a faithful projection / defect-discharge domain.

This file deliberately keeps the atom predicate abstract.  The concrete
SaturationMonoid specialization should instantiate it with the existing
`NatMultiplicativelyAtomic` bridge, not a naked prime predicate.

The only Mathlib import is the `Even` predicate needed by the uniform
non-prime toy family at the bottom of the file.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Natural-number multiplicative atom predicate for the theorem-design
socket.

This is intentionally phrased in the multiplicative monoid of natural numbers:
`1` is the unit, and every factorization of an atom has a unit side.  It does
not mention `Nat.Prime` and does not give any additive closure of atoms. -/
def NatMultiplicativelyAtomic (m : Nat) : Prop :=
  m ≠ 1 ∧
    ∀ {a b : Nat}, m = a * b -> a = 1 ∨ b = 1

/-- A natural code together with evidence that it is an atom for the intended
multiplicative arithmetic structure. -/
structure MultiplicativeAtomCode (Atomic : Nat -> Prop) where
  code : Nat
  atomic : Atomic code

/-- Concrete code object for atoms of the natural-number multiplicative
monoid. -/
abbrev NatMultiplicativeAtomCode :=
  MultiplicativeAtomCode NatMultiplicativelyAtomic

/-- Product of a list of multiplicative atom codes. -/
def multiplicativeAtomCodeProduct
    {Atomic : Nat -> Prop} :
    List (MultiplicativeAtomCode Atomic) -> Nat
  | [] => 1
  | x :: xs => x.code * multiplicativeAtomCodeProduct xs

@[simp]
theorem multiplicativeAtomCodeProduct_singleton
    {Atomic : Nat -> Prop}
    (a : MultiplicativeAtomCode Atomic) :
    multiplicativeAtomCodeProduct [a] = a.code := by
  exact Nat.mul_one a.code

/-- An arithmetic atom pair in the even fiber `2 * n`.  Atomhood is
multiplicative; the energy shell is additive. -/
structure ArithmeticAtomPair (Atomic : Nat -> Prop) (n : Nat) where
  left : MultiplicativeAtomCode Atomic
  right : MultiplicativeAtomCode Atomic

namespace ArithmeticAtomPair

/-- Signed additive residual of an atom pair in the even fiber `2 * n`. -/
def residual {Atomic : Nat -> Prop} {n : Nat}
    (p : ArithmeticAtomPair Atomic n) : Int :=
  ((2 * n : Nat) : Int) - ((p.left.code + p.right.code : Nat) : Int)

/-- Absolute residual energy of an atom pair. -/
def energy {Atomic : Nat -> Prop} {n : Nat}
    (p : ArithmeticAtomPair Atomic n) : Nat :=
  Int.natAbs p.residual

end ArithmeticAtomPair

/-- Additive residual transport side.

This is where `E -> E - 1` motion belongs.  It does not assert that any
multiplicative atom pair exists at the target shell. -/
structure AdditiveResidualTransportCategory
    (SourceEvidence : Type u) where
  residualEnergy : SourceEvidence -> Nat
  step : SourceEvidence -> SourceEvidence -> Prop
  step_decreases_one :
    ∀ {source target : SourceEvidence},
      step source target ->
        residualEnergy target + 1 = residualEnergy source

/-- Source-side representation repair demand at residual shell `k`.

`SourceEvidence` is intentionally opaque here: concrete versions should package
representation / GT / crystal / branching data together with source path,
phase trace, sigma tag, and producer trace.

The residual shell is read from the additive transport object.  This prevents a
demand from carrying an unrelated self-reported energy value. -/
structure RepRepairDemand
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n k : Nat) where
  evidence : SourceEvidence
  residual_eq : Residual.residualEnergy evidence = k

/-- Multiplicative atom factorization side.

This is intentionally not an additive closure structure.  It records atom
objects and a factorization relation in the multiplicative arithmetic world.
-/
structure MultiplicativeAtomFactorizationCategory
    (Atomic : Nat -> Prop) where
  factors : Nat -> List (MultiplicativeAtomCode Atomic) -> Prop
  factor_product : List (MultiplicativeAtomCode Atomic) -> Nat
  atom_factorizes_self :
    ∀ a : MultiplicativeAtomCode Atomic, factors a.code [a]
  factorization_reads_product :
    ∀ {m : Nat} {xs : List (MultiplicativeAtomCode Atomic)},
      factors m xs -> factor_product xs = m

/-- Canonical factorization category obtained from list product of atom codes.

This does not assert that arbitrary naturals factor into atoms; it only
provides the self-factorization and product readout needed by already-produced
atom-pair objects. -/
def listProductMultiplicativeAtomFactorizationCategory
    (Atomic : Nat -> Prop) :
    MultiplicativeAtomFactorizationCategory Atomic where
  factors := fun m xs => multiplicativeAtomCodeProduct xs = m
  factor_product := multiplicativeAtomCodeProduct
  atom_factorizes_self := by
    intro a
    exact multiplicativeAtomCodeProduct_singleton a
  factorization_reads_product := by
    intro m xs h
    exact h

/-- Natural-number multiplicative atom factorization category. -/
def natMultiplicativeAtomFactorizationCategory :
    MultiplicativeAtomFactorizationCategory NatMultiplicativelyAtomic :=
  listProductMultiplicativeAtomFactorizationCategory
    NatMultiplicativelyAtomic

/-- Factorization-category readout for the two endpoints of an arithmetic
atom pair.  This keeps endpoint admissibility in the multiplicative world; it
does not assert any additive closure of atoms. -/
structure ArithmeticAtomPairFactorizationReadout
    (Atomic : Nat -> Prop)
    (F : MultiplicativeAtomFactorizationCategory Atomic)
    {n : Nat}
    (p : ArithmeticAtomPair Atomic n) where
  left_factors_self : F.factors p.left.code [p.left]
  right_factors_self : F.factors p.right.code [p.right]
  left_factor_product_eq :
    F.factor_product [p.left] = p.left.code
  right_factor_product_eq :
    F.factor_product [p.right] = p.right.code

/-- Any `ArithmeticAtomPair` carries endpoint factorization readout from the
multiplicative atom factorization category. -/
theorem factorizationReadoutOfAtomPair
    {Atomic : Nat -> Prop}
    (F : MultiplicativeAtomFactorizationCategory Atomic)
    {n : Nat}
    (p : ArithmeticAtomPair Atomic n) :
    ArithmeticAtomPairFactorizationReadout Atomic F p := by
  refine {
    left_factors_self := F.atom_factorizes_self p.left
    right_factors_self := F.atom_factorizes_self p.right
    left_factor_product_eq :=
      F.factorization_reads_product (F.atom_factorizes_self p.left)
    right_factor_product_eq :=
      F.factorization_reads_product (F.atom_factorizes_self p.right)
  }

/-- Atom-pair realization strengthened with multiplicative factorization
readout for both endpoints.

This is kept as a `Prop`, not a witness-carrying `Type`, so it can be derived
from ordinary existential realization theorems without adding choice or
computational extraction. -/
def FactorizedAtomPairRealization
    (Atomic : Nat -> Prop)
    (F : MultiplicativeAtomFactorizationCategory Atomic)
    (n k : Nat) : Prop :=
  ∃ p : ArithmeticAtomPair Atomic n,
    ArithmeticAtomPair.energy p = k ∧
      ArithmeticAtomPairFactorizationReadout Atomic F p

/-- Package a realized atom pair with its endpoint factorization readout. -/
theorem factorizedAtomPairRealizationOfPair
    {Atomic : Nat -> Prop}
    (F : MultiplicativeAtomFactorizationCategory Atomic)
    {n k : Nat}
    (p : ArithmeticAtomPair Atomic n)
    (hEnergy : ArithmeticAtomPair.energy p = k) :
    FactorizedAtomPairRealization Atomic F n k :=
  ⟨p, hEnergy, factorizationReadoutOfAtomPair F p⟩

/-- Representation/source feasible category.

The concrete version should be a GT/crystal/branching/source-path category.
Here we require only the category-like data needed by the defect socket. -/
structure RepresentationFeasibleCategory
    (SourceEvidence : Type u) where
  feasible : SourceEvidence -> Prop
  path : SourceEvidence -> SourceEvidence -> Prop
  path_preserves_feasible :
    ∀ {source target : SourceEvidence},
      path source target -> feasible source -> feasible target

/-- A repair demand whose source evidence is feasible in the representation
category.

The older `RepRepairDemand` only records a residual shell.  This wrapper is
the source-side object intended by the research target: an active demand must
come from the feasible representation/source category, not from an arbitrary
endpoint-code or residual witness. -/
structure FeasibleRepRepairDemand
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n k : Nat) where
  demand : RepRepairDemand SourceEvidence Residual n k
  feasible : Source.feasible demand.evidence

/-- Source-side repair trace carried by an active representation repair demand.

The four fields mirror the intended source object: source path, phase trace,
sigma tag, and producer trace.  The types remain abstract so a future
GT/crystal/branching instance can supply its native trace objects. -/
structure SourceRepairTrace
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u) where
  sourcePath : SourcePath
  phaseTrace : PhaseTrace
  sigmaTag : SigmaTag
  producerTrace : ProducerTrace

/-- Feasible repair demand equipped with its source-production trace.

This is the stronger source-side socket: a demand is not merely a residual
shell with feasible evidence; it also keeps the route by which the source
producer generated the repair obligation. -/
structure TracedFeasibleRepRepairDemand
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n k : Nat) where
  demand : FeasibleRepRepairDemand SourceEvidence Residual Source n k
  trace : SourceRepairTrace SourcePath PhaseTrace SigmaTag ProducerTrace

/-- Raw endpoint-code pair before multiplicative atom certification.

This is the code-projection layer.  It deliberately carries only natural
endpoint codes and additive residual energy; atomhood is supplied separately
by `AtomicEndpointCodeProjection`. -/
structure EndpointCodePair (n : Nat) where
  leftCode : Nat
  rightCode : Nat

namespace EndpointCodePair

/-- Signed additive residual of a raw endpoint-code pair. -/
def residual {n : Nat} (c : EndpointCodePair n) : Int :=
  ((2 * n : Nat) : Int) - ((c.leftCode + c.rightCode : Nat) : Int)

/-- Absolute residual energy of a raw endpoint-code pair. -/
def energy {n : Nat} (c : EndpointCodePair n) : Nat :=
  Int.natAbs c.residual

end EndpointCodePair

/-- Upgrade a raw endpoint-code pair to an arithmetic atom pair once both
endpoints have multiplicative atom certification. -/
def atomPairOfEndpointCodePair
    {Atomic : Nat -> Prop} {n : Nat}
    (c : EndpointCodePair n)
    (hLeft : Atomic c.leftCode)
    (hRight : Atomic c.rightCode) :
    ArithmeticAtomPair Atomic n where
  left := {
    code := c.leftCode
    atomic := hLeft
  }
  right := {
    code := c.rightCode
    atomic := hRight
  }

/-- The upgrade from raw endpoint codes to atom-pair objects preserves the
additive residual energy definition. -/
theorem atomPairOfEndpointCodePair_energy
    {Atomic : Nat -> Prop} {n : Nat}
    (c : EndpointCodePair n)
    (hLeft : Atomic c.leftCode)
    (hRight : Atomic c.rightCode) :
    ArithmeticAtomPair.energy
      (atomPairOfEndpointCodePair c hLeft hRight) =
    EndpointCodePair.energy c := rfl

/-- Faithful source-to-endpoint-code projection.

This projection has not yet passed the multiplicative atom filter.  It only
asserts that when source evidence projects to endpoint codes, their additive
energy agrees with the source residual energy. -/
structure FaithfulEndpointCodeProjection
    (SourceEvidence : Type u) (n : Nat)
    (Residual : AdditiveResidualTransportCategory SourceEvidence) where
  projectCode : SourceEvidence -> Option (EndpointCodePair n)
  code_energy_faithful :
    ∀ {s : SourceEvidence} {c : EndpointCodePair n},
      projectCode s = some c ->
        EndpointCodePair.energy c = Residual.residualEnergy s

/-- Endpoint-code projection plus endpoint atomicity certification.

This is the split version of the old direct atom-pair projection: first read
raw endpoint codes, then certify that both projected endpoint codes are atoms
in the multiplicative arithmetic world. -/
structure AtomicEndpointCodeProjection
    (Atomic : Nat -> Prop) (SourceEvidence : Type u) (n : Nat)
    (Residual : AdditiveResidualTransportCategory SourceEvidence) where
  codeProjection :
    FaithfulEndpointCodeProjection SourceEvidence n Residual
  left_atomic :
    ∀ {s : SourceEvidence} {c : EndpointCodePair n},
      codeProjection.projectCode s = some c -> Atomic c.leftCode
  right_atomic :
    ∀ {s : SourceEvidence} {c : EndpointCodePair n},
      codeProjection.projectCode s = some c -> Atomic c.rightCode

/-- Endpoint-code projection certified by natural-number multiplicative atoms.
-/
abbrev NatAtomicEndpointCodeProjection
    (SourceEvidence : Type u) (n : Nat)
    (Residual : AdditiveResidualTransportCategory SourceEvidence) :=
  AtomicEndpointCodeProjection
    NatMultiplicativelyAtomic SourceEvidence n Residual

/-- A defined endpoint-code projection contains some raw endpoint-code pair. -/
theorem projected_endpoint_code_pair_of_code_projection_defined
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (Projection :
      FaithfulEndpointCodeProjection SourceEvidence n Residual)
    (evidence : SourceEvidence)
    (hDefined : Projection.projectCode evidence ≠ none) :
    ∃ c : EndpointCodePair n,
      Projection.projectCode evidence = some c := by
  cases hProject : Projection.projectCode evidence with
  | none =>
      exact False.elim (hDefined hProject)
  | some c =>
      exact ⟨c, rfl⟩

/-- A source demand whose endpoint-code projection is present and atomically
certified gives an arithmetic atom-pair realization at the demanded shell. -/
theorem atom_pair_realization_of_atomic_code_projected_demand
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual)
    (demand : RepRepairDemand SourceEvidence Residual n k)
    (hProject :
      ∃ c : EndpointCodePair n,
        Projection.codeProjection.projectCode demand.evidence = some c) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k := by
  rcases hProject with ⟨c, hc⟩
  refine
    ⟨atomPairOfEndpointCodePair
        c (Projection.left_atomic hc) (Projection.right_atomic hc), ?_⟩
  calc
    ArithmeticAtomPair.energy
        (atomPairOfEndpointCodePair
          c (Projection.left_atomic hc) (Projection.right_atomic hc)) =
        EndpointCodePair.energy c :=
      atomPairOfEndpointCodePair_energy
        c (Projection.left_atomic hc) (Projection.right_atomic hc)
    _ = Residual.residualEnergy demand.evidence :=
      Projection.codeProjection.code_energy_faithful hc
    _ = k := demand.residual_eq

/-- A source demand whose endpoint-code projection is defined and atomically
certified gives an arithmetic atom-pair realization. -/
theorem atom_pair_realization_of_atomic_code_defined_demand
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual)
    (demand : RepRepairDemand SourceEvidence Residual n k)
    (hDefined :
      Projection.codeProjection.projectCode demand.evidence ≠ none) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  atom_pair_realization_of_atomic_code_projected_demand
    Projection demand
    (projected_endpoint_code_pair_of_code_projection_defined
      Projection.codeProjection demand.evidence hDefined)

/-- Specialized endpoint-code readout for the natural-number multiplicative
atom predicate. -/
theorem atom_pair_realization_of_nat_atom_code_defined_demand
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (Projection :
      NatAtomicEndpointCodeProjection SourceEvidence n Residual)
    (demand : RepRepairDemand SourceEvidence Residual n k)
    (hDefined :
      Projection.codeProjection.projectCode demand.evidence ≠ none) :
    ∃ p : ArithmeticAtomPair NatMultiplicativelyAtomic n,
      ArithmeticAtomPair.energy p = k :=
  atom_pair_realization_of_atomic_code_defined_demand
    Projection demand hDefined

/-- Faithful source-to-atom projection.

The projection is partial: a missing projection is exactly what a defect
records.  Faithfulness says that whenever a projection is present, the
arithmetic atom-pair energy reads the additive source residual. -/
structure FaithfulAtomProjectionFunctor
    (Atomic : Nat -> Prop) (SourceEvidence : Type u) (n : Nat)
    (Residual : AdditiveResidualTransportCategory SourceEvidence) where
  project : SourceEvidence -> Option (ArithmeticAtomPair Atomic n)
  energy_faithful :
    ∀ {s : SourceEvidence} {p : ArithmeticAtomPair Atomic n},
      project s = some p -> ArithmeticAtomPair.energy p = Residual.residualEnergy s

/-- Explicit compatibility readout between split endpoint-code projection and
the older direct atom-pair projection functor.

This certificate is intentionally not hidden inside
`AtomicEndpointCodeProjection`: constructing a direct atom-pair projection from
raw endpoint codes requires transporting endpoint atomicity proofs.  Future
instances may supply this readout, and then the old direct-projection route can
be reused without erasing the code-projection obligations. -/
structure AtomicCodeProjectionDirectReadout
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (CodeProjection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual) where
  atomProjection :
    FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual
  atom_projection_none_iff_code_projection_none :
    ∀ evidence : SourceEvidence,
      atomProjection.project evidence = none ↔
        CodeProjection.codeProjection.projectCode evidence = none
  atom_projection_defined_iff_code_projection_defined :
    ∀ evidence : SourceEvidence,
      atomProjection.project evidence ≠ none ↔
        CodeProjection.codeProjection.projectCode evidence ≠ none

/-- A source demand whose evidence is actually projected by a faithful
projection functor gives an atom-pair realization at the demanded shell.

This is the minimal readout bridge from source repair demand to arithmetic
atom-pair realization.  It does not search endpoints; the atom pair must come
from the projection functor. -/
theorem atom_pair_realization_of_projected_demand
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual)
    (demand : RepRepairDemand SourceEvidence Residual n k)
    (hProject :
      ∃ p : ArithmeticAtomPair Atomic n,
        Projection.project demand.evidence = some p) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k := by
  rcases hProject with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  calc
    ArithmeticAtomPair.energy p =
        Residual.residualEnergy demand.evidence :=
      Projection.energy_faithful hp
    _ = k := demand.residual_eq

/-- A defined partial projection contains some atom-pair object.

This separates the source-side obligation "the projection is defined here"
from the arithmetic object returned by the projection functor. -/
theorem projected_pair_of_projection_defined
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual)
    (evidence : SourceEvidence)
    (hDefined : Projection.project evidence ≠ none) :
    ∃ p : ArithmeticAtomPair Atomic n,
      Projection.project evidence = some p := by
  cases hProject : Projection.project evidence with
  | none =>
      exact False.elim (hDefined hProject)
  | some p =>
      exact ⟨p, rfl⟩

/-- A source demand whose projection is defined gives an atom-pair
realization at the demanded shell. -/
theorem atom_pair_realization_of_defined_projected_demand
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual)
    (demand : RepRepairDemand SourceEvidence Residual n k)
    (hDefined : Projection.project demand.evidence ≠ none) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  atom_pair_realization_of_projected_demand
    Projection
    demand
    (projected_pair_of_projection_defined
      Projection demand.evidence hDefined)

/-- Defect dynamics / discharge principle.

This is the hard future theorem packaged as its own component.  It must be
earned from transport, projection, finite descent / holonomy, and no-third-sink
structure, not from endpoint coverage. -/
structure AtomProjectionDefectDischargeLaw
    (Atomic : Nat -> Prop) (SourceEvidence : Type u) (n : Nat)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  defect_propagates_or_discharges : Prop
  finite_descent_or_holonomy_bound : Prop
  no_third_sink_or_naked_terminal_defect : Prop
  realization_of_demand :
    ∀ {k : Nat},
      RepRepairDemand SourceEvidence Residual n k ->
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k

/-- Feasible-scoped defect discharge law.

This is the better target for source/representation instantiations: it only
has to realize repair demands whose evidence is feasible in the source
category.  The older all-demand law remains useful as a stronger socket, but
should not be mistaken for the minimal source-side obligation. -/
structure FeasibleAtomProjectionDefectDischargeLaw
    (Atomic : Nat -> Prop) (SourceEvidence : Type u) (n : Nat)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  defect_propagates_or_discharges : Prop
  finite_descent_or_holonomy_bound : Prop
  no_third_sink_or_naked_terminal_defect : Prop
  realization_of_feasible_demand :
    ∀ {k : Nat},
      FeasibleRepRepairDemand SourceEvidence Residual Source n k ->
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k

/-- Projection defect: source-side repair demand exists at shell `k`, but no
multiplicative atom pair realizes that additive shell. -/
structure AtomProjectionDefect
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n k : Nat) where
  demand : RepRepairDemand SourceEvidence Residual n k
  noAtomRealization :
    ¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k

/-- Feasible projection defect: a feasible source-side repair demand exists at
shell `k`, but no multiplicative atom pair realizes that additive shell.

This is the sharper obstruction object for future GT/crystal/branching
instances. -/
structure FeasibleAtomProjectionDefect
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n k : Nat) where
  demand : FeasibleRepRepairDemand SourceEvidence Residual Source n k
  noAtomRealization :
    ¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k

/-- Traced feasible projection defect: the missing atom-pair realization is
attached to an active feasible source demand together with its production
trace. -/
structure TracedFeasibleAtomProjectionDefect
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n k : Nat) where
  demand :
    TracedFeasibleRepRepairDemand
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n k
  noAtomRealization :
    ¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k

/-- Stable transport/projection domain.

The component fields prevent this from being a single opaque "magic bridge" in
the theorem statement.  The nested `discharge_law` is the hard theorem future
work must earn from the preceding structures, not from endpoint-table coverage.
-/
structure StableTransportAtomProjectionDomain
    (Atomic : Nat -> Prop) (SourceEvidence : Type u) (n : Nat) where
  multiplicative_atoms : MultiplicativeAtomFactorizationCategory Atomic
  residual_transport : AdditiveResidualTransportCategory SourceEvidence
  source_category : RepresentationFeasibleCategory SourceEvidence
  projection_functor :
    FaithfulAtomProjectionFunctor Atomic SourceEvidence n residual_transport
  discharge_law :
    AtomProjectionDefectDischargeLaw
      Atomic SourceEvidence n residual_transport source_category
      projection_functor

/-- Feasible-scoped stable transport/projection domain.

The discharge law only speaks about feasible source repair demands.  This is
the intended theorem socket when the source category is a genuine
GT/crystal/branching feasible category. -/
structure FeasibleStableTransportAtomProjectionDomain
    (Atomic : Nat -> Prop) (SourceEvidence : Type u) (n : Nat) where
  multiplicative_atoms : MultiplicativeAtomFactorizationCategory Atomic
  residual_transport : AdditiveResidualTransportCategory SourceEvidence
  source_category : RepresentationFeasibleCategory SourceEvidence
  projection_functor :
    FaithfulAtomProjectionFunctor Atomic SourceEvidence n residual_transport
  discharge_law :
    FeasibleAtomProjectionDefectDischargeLaw
      Atomic SourceEvidence n residual_transport source_category
      projection_functor

/-- A stronger all-demand stable domain induces the feasible-scoped one. -/
def feasibleStableTransportAtomProjectionDomainOfStable
    {Atomic : Nat -> Prop} {SourceEvidence : Type u} {n : Nat}
    (D : StableTransportAtomProjectionDomain Atomic SourceEvidence n) :
    FeasibleStableTransportAtomProjectionDomain Atomic SourceEvidence n where
  multiplicative_atoms := D.multiplicative_atoms
  residual_transport := D.residual_transport
  source_category := D.source_category
  projection_functor := D.projection_functor
  discharge_law := {
    defect_propagates_or_discharges :=
      D.discharge_law.defect_propagates_or_discharges
    finite_descent_or_holonomy_bound :=
      D.discharge_law.finite_descent_or_holonomy_bound
    no_third_sink_or_naked_terminal_defect :=
      D.discharge_law.no_third_sink_or_naked_terminal_defect
    realization_of_feasible_demand := by
      intro k demand
      exact D.discharge_law.realization_of_demand demand.demand
  }

/-- The core theorem-design socket: a stable atom-projection domain forbids
projection defects. -/
theorem no_stable_atom_projection_defect
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {n k : Nat}
    (D : StableTransportAtomProjectionDomain Atomic SourceEvidence n) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence D.residual_transport n k) := by
  intro hdefect
  rcases hdefect with ⟨defect⟩
  exact defect.noAtomRealization
    (D.discharge_law.realization_of_demand defect.demand)

/-- Feasible-scoped stable domains forbid feasible atom-projection defects. -/
theorem no_feasible_stable_atom_projection_defect
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {n k : Nat}
    (D :
      FeasibleStableTransportAtomProjectionDomain
        Atomic SourceEvidence n) :
    ¬ Nonempty
      (FeasibleAtomProjectionDefect
        Atomic SourceEvidence D.residual_transport D.source_category n k) := by
  intro hdefect
  rcases hdefect with ⟨defect⟩
  exact defect.noAtomRealization
    (D.discharge_law.realization_of_feasible_demand defect.demand)

/-- Constructing an atom-pair realization discharges the defect predicate for
one demand.  This is useful for local slices that produce a single projected
atom pair rather than a whole stable domain. -/
theorem not_defect_of_atom_realization
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (realization :
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) := by
  intro hdefect
  rcases hdefect with ⟨defect⟩
  exact defect.noAtomRealization realization

/-- A realized atom pair also discharges the feasible-scoped defect predicate
for one demand. -/
theorem not_feasible_defect_of_atom_realization
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (realization :
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k) :
    ¬ Nonempty
      (FeasibleAtomProjectionDefect
        Atomic SourceEvidence Residual Source n k) := by
  intro hdefect
  rcases hdefect with ⟨defect⟩
  exact defect.noAtomRealization realization

/-- A realized atom pair discharges the traced feasible defect predicate. -/
theorem not_traced_feasible_defect_of_atom_realization
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (realization :
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) := by
  intro hdefect
  rcases hdefect with ⟨defect⟩
  exact defect.noAtomRealization realization

/-- A defined atomic endpoint-code projection discharges the feasible defect
predicate for one feasible demand. -/
theorem not_feasible_defect_of_atomic_code_defined_demand
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual)
    (demand :
      FeasibleRepRepairDemand SourceEvidence Residual Source n k)
    (hDefined :
      Projection.codeProjection.projectCode demand.demand.evidence ≠ none) :
    ¬ Nonempty
      (FeasibleAtomProjectionDefect
        Atomic SourceEvidence Residual Source n k) :=
  not_feasible_defect_of_atom_realization
    (atom_pair_realization_of_atomic_code_defined_demand
      Projection demand.demand hDefined)

/-- Specialized feasible-defect discharge for natural-number multiplicative
atom endpoint-code projection. -/
theorem not_feasible_defect_of_nat_atom_code_defined_demand
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (Projection :
      NatAtomicEndpointCodeProjection SourceEvidence n Residual)
    (demand :
      FeasibleRepRepairDemand SourceEvidence Residual Source n k)
    (hDefined :
      Projection.codeProjection.projectCode demand.demand.evidence ≠ none) :
    ¬ Nonempty
      (FeasibleAtomProjectionDefect
        NatMultiplicativelyAtomic SourceEvidence Residual Source n k) :=
  not_feasible_defect_of_atomic_code_defined_demand
    Projection demand hDefined

/-- Specialized local discharge for traced feasible demands using
natural-number multiplicative atom endpoint-code projection. -/
theorem not_traced_feasible_defect_of_nat_atom_code_defined_demand
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (Projection :
      NatAtomicEndpointCodeProjection SourceEvidence n Residual)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k)
    (hDefined :
      Projection.codeProjection.projectCode demand.demand.demand.evidence ≠
        none) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        NatMultiplicativelyAtomic SourceEvidence Residual Source n k) :=
  not_traced_feasible_defect_of_atom_realization
    (atom_pair_realization_of_nat_atom_code_defined_demand
      Projection demand.demand.demand hDefined)

/-!
## Atom-projection defect finite descent socket

The witness-return discharge law above is intentionally strong: it produces an
atom pair.  The next socket is weaker and closer to the sigma-blueprint shape.
It proves that a stable projection defect cannot persist when:

* terminal defects are ruled out by a no-third-sink disposition; and
* every positive defect descends to the preceding residual shell.

This does not construct an atom pair.  For a concrete demand it yields the
constructive conclusion `¬¬ atom-pair realization`, leaving witness extraction
to a later constructive/classical bridge.
-/

/-- Terminal no-third-sink law specialized to atom-projection defects. -/
structure AtomProjectionTerminalNoThirdSink
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat) where
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  absorbed_static : Prop
  projected_repair : Prop
  no_third_sink :
    Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n 0) ->
      headroom_nonzero ->
        absorbed_static ∨ projected_repair
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  defect_forbids_projected_repair :
    Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n 0) ->
      ¬ projected_repair

/-- Terminal no-third-sink law with a materialized projected-repair branch.

This strengthens `AtomProjectionTerminalNoThirdSink` by making the
`projected_repair` branch carry real arithmetic content: if that branch is
chosen, an atom-pair realization at the terminal shell exists.  Therefore a
terminal defect itself forbids the branch; that prohibition is no longer a
separate primitive field. -/
structure AtomProjectionTerminalMaterializingNoThirdSink
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat) where
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  absorbed_static : Prop
  projected_repair : Prop
  no_third_sink :
    Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n 0) ->
      headroom_nonzero ->
        absorbed_static ∨ projected_repair
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  projected_repair_realizes :
    projected_repair ->
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = 0

/-- Terminal projected-repair readout through the faithful projection functor.

The `projected_repair` branch is no longer just a proposition that promises a
witness.  It must identify a terminal source demand and show that the faithful
projection functor actually materializes that demand as `some` atom pair. -/
structure TerminalProjectedRepairReadout
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  projected_repair : Prop
  terminal_demand :
    projected_repair ->
      RepRepairDemand SourceEvidence Residual n 0
  projected_pair :
    ∀ hProjected : projected_repair,
      ∃ p : ArithmeticAtomPair Atomic n,
        Projection.project (terminal_demand hProjected).evidence = some p

/-- Terminal projected-repair readout that only asserts the faithful partial
projection is defined at the terminal demand.

The atom-pair object is then read from `Projection.project`; it is not supplied
as a separate branch witness. -/
structure TerminalProjectionDefinedReadout
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  projected_repair : Prop
  terminal_demand :
    projected_repair ->
      RepRepairDemand SourceEvidence Residual n 0
  projection_defined :
    ∀ hProjected : projected_repair,
      Projection.project (terminal_demand hProjected).evidence ≠ none

/-- Terminal projected-repair readout where projection failure is absorbed.

This is a source-side shape: if the projected branch is chosen but the partial
projection is undefined on the terminal demand, the state must have fallen into
`absorbed_static`.  A nonzero-headroom terminal law can then rule that out and
derive that the projection is defined. -/
structure TerminalProjectionNonabsorbedReadout
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual)
    (absorbed_static : Prop) where
  projected_repair : Prop
  terminal_demand :
    projected_repair ->
      RepRepairDemand SourceEvidence Residual n 0
  projection_undefined_absorbs :
    ∀ hProjected : projected_repair,
      Projection.project (terminal_demand hProjected).evidence = none ->
        absorbed_static

/-- A nonabsorbed projected-repair readout gives defined projection once the
ambient terminal law rules out `absorbed_static`. -/
theorem projection_defined_of_nonabsorbed_readout
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    {absorbed_static : Prop}
    (R :
      TerminalProjectionNonabsorbedReadout
        Atomic SourceEvidence Residual n Projection absorbed_static)
    (hNotAbsorbed : ¬ absorbed_static) :
    ∀ hProjected : R.projected_repair,
      Projection.project (R.terminal_demand hProjected).evidence ≠ none := by
  intro hProjected hNone
  exact hNotAbsorbed
    (R.projection_undefined_absorbs hProjected hNone)

/-- A nonabsorbed readout induces a defined-projection readout once absorption
has been ruled out. -/
def terminalProjectionDefinedReadoutOfNonabsorbed
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    {absorbed_static : Prop}
    (R :
      TerminalProjectionNonabsorbedReadout
        Atomic SourceEvidence Residual n Projection absorbed_static)
    (hNotAbsorbed : ¬ absorbed_static) :
    TerminalProjectionDefinedReadout
      Atomic SourceEvidence Residual n Projection where
  projected_repair := R.projected_repair
  terminal_demand := R.terminal_demand
  projection_defined :=
    projection_defined_of_nonabsorbed_readout R hNotAbsorbed

/-- A defined projection readout induces the older explicit projected-pair
readout by opening the `Option` returned by the projection functor. -/
def terminalProjectedRepairReadoutOfDefined
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (R :
      TerminalProjectionDefinedReadout
        Atomic SourceEvidence Residual n Projection) :
    TerminalProjectedRepairReadout
      Atomic SourceEvidence Residual n Projection where
  projected_repair := R.projected_repair
  terminal_demand := R.terminal_demand
  projected_pair := fun hProjected =>
    projected_pair_of_projection_defined
      Projection
      (R.terminal_demand hProjected).evidence
      (R.projection_defined hProjected)

/-- A projected-repair readout materializes the terminal atom-pair
realization by projection faithfulness. -/
theorem projected_repair_realizes_of_terminal_readout
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (R :
      TerminalProjectedRepairReadout
        Atomic SourceEvidence Residual n Projection) :
    R.projected_repair ->
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = 0 := by
  intro hProjected
  exact
    atom_pair_realization_of_projected_demand
      Projection
      (R.terminal_demand hProjected)
      (R.projected_pair hProjected)

/-- A defined projection readout materializes the terminal atom-pair
realization by projection faithfulness. -/
theorem projected_repair_realizes_of_terminal_defined_readout
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (R :
      TerminalProjectionDefinedReadout
        Atomic SourceEvidence Residual n Projection) :
    R.projected_repair ->
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = 0 := by
  intro hProjected
  exact
    atom_pair_realization_of_defined_projected_demand
      Projection
      (R.terminal_demand hProjected)
      (R.projection_defined hProjected)

/-- Terminal no-third-sink where the projected branch is read through the
faithful projection functor.  This is stronger than the materializing law:
materialization is derived from `Projection.project = some p` plus
`energy_faithful`. -/
structure AtomProjectionTerminalProjectedNoThirdSink
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  absorbed_static : Prop
  projected_readout :
    TerminalProjectedRepairReadout
      Atomic SourceEvidence Residual n Projection
  no_third_sink :
    Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n 0) ->
      headroom_nonzero ->
        absorbed_static ∨ projected_readout.projected_repair
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static

/-- Terminal no-third-sink where the projected branch only asserts that the
faithful partial projection is defined on the terminal demand. -/
structure AtomProjectionTerminalDefinedNoThirdSink
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  absorbed_static : Prop
  projected_readout :
    TerminalProjectionDefinedReadout
      Atomic SourceEvidence Residual n Projection
  no_third_sink :
    Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n 0) ->
      headroom_nonzero ->
        absorbed_static ∨ projected_readout.projected_repair
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static

/-- Terminal no-third-sink where the projected branch is nonabsorbed:
projection failure would force the absorbed-static branch, which nonzero
headroom rules out. -/
structure AtomProjectionTerminalNonabsorbedNoThirdSink
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  absorbed_static : Prop
  projected_readout :
    TerminalProjectionNonabsorbedReadout
      Atomic SourceEvidence Residual n Projection absorbed_static
  no_third_sink :
    Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n 0) ->
      headroom_nonzero ->
        absorbed_static ∨ projected_readout.projected_repair
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static

/-- A projected no-third-sink law induces the materializing terminal law by
using the faithful projection readout. -/
def atomProjectionTerminalMaterializingNoThirdSinkOfProjected
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      AtomProjectionTerminalProjectedNoThirdSink
        Atomic SourceEvidence Residual n Projection) :
    AtomProjectionTerminalMaterializingNoThirdSink
      Atomic SourceEvidence Residual n where
  headroom_nonzero := L.headroom_nonzero
  headroom_witness := L.headroom_witness
  absorbed_static := L.absorbed_static
  projected_repair := L.projected_readout.projected_repair
  no_third_sink := L.no_third_sink
  nonzero_forbids_absorbed_static :=
    L.nonzero_forbids_absorbed_static
  projected_repair_realizes :=
    projected_repair_realizes_of_terminal_readout
      L.projected_readout

/-- A defined no-third-sink law induces the projected terminal law by opening
the partial projection's `Option` value. -/
def atomProjectionTerminalProjectedNoThirdSinkOfDefined
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      AtomProjectionTerminalDefinedNoThirdSink
        Atomic SourceEvidence Residual n Projection) :
    AtomProjectionTerminalProjectedNoThirdSink
      Atomic SourceEvidence Residual n Projection where
  headroom_nonzero := L.headroom_nonzero
  headroom_witness := L.headroom_witness
  absorbed_static := L.absorbed_static
  projected_readout :=
    terminalProjectedRepairReadoutOfDefined
      L.projected_readout
  no_third_sink := L.no_third_sink
  nonzero_forbids_absorbed_static :=
    L.nonzero_forbids_absorbed_static

/-- A defined no-third-sink law induces the materializing terminal law by
faithful projection readout. -/
def atomProjectionTerminalMaterializingNoThirdSinkOfDefined
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      AtomProjectionTerminalDefinedNoThirdSink
        Atomic SourceEvidence Residual n Projection) :
    AtomProjectionTerminalMaterializingNoThirdSink
      Atomic SourceEvidence Residual n :=
  atomProjectionTerminalMaterializingNoThirdSinkOfProjected
    (atomProjectionTerminalProjectedNoThirdSinkOfDefined L)

/-- A nonabsorbed terminal law induces the defined terminal law by using
nonzero headroom to rule out absorbed-static projection failure. -/
def atomProjectionTerminalDefinedNoThirdSinkOfNonabsorbed
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection) :
    AtomProjectionTerminalDefinedNoThirdSink
      Atomic SourceEvidence Residual n Projection where
  headroom_nonzero := L.headroom_nonzero
  headroom_witness := L.headroom_witness
  absorbed_static := L.absorbed_static
  projected_readout :=
    terminalProjectionDefinedReadoutOfNonabsorbed
      L.projected_readout
      (L.nonzero_forbids_absorbed_static L.headroom_witness)
  no_third_sink := L.no_third_sink
  nonzero_forbids_absorbed_static :=
    L.nonzero_forbids_absorbed_static

/-- A nonabsorbed terminal law induces the materializing terminal law by
deriving defined projection and then reading the faithful projection value. -/
def atomProjectionTerminalMaterializingNoThirdSinkOfNonabsorbed
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection) :
    AtomProjectionTerminalMaterializingNoThirdSink
      Atomic SourceEvidence Residual n :=
  atomProjectionTerminalMaterializingNoThirdSinkOfDefined
    (atomProjectionTerminalDefinedNoThirdSinkOfNonabsorbed L)

/-- A materializing no-third-sink law induces the older terminal law by reading
`¬ projected_repair` from the defect's missing-realization side. -/
def atomProjectionTerminalNoThirdSinkOfMaterializing
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (L :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n) :
    AtomProjectionTerminalNoThirdSink
      Atomic SourceEvidence Residual n where
  headroom_nonzero := L.headroom_nonzero
  headroom_witness := L.headroom_witness
  absorbed_static := L.absorbed_static
  projected_repair := L.projected_repair
  no_third_sink := L.no_third_sink
  nonzero_forbids_absorbed_static :=
    L.nonzero_forbids_absorbed_static
  defect_forbids_projected_repair := by
    intro hDefect hProjected
    rcases hDefect with ⟨defect⟩
    exact defect.noAtomRealization
      (L.projected_repair_realizes hProjected)

/-- Terminal atom-projection defects are impossible under the two-branch
no-third-sink disposition. -/
theorem no_terminal_atom_projection_defect_of_no_third_sink
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (L :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n) :
    ¬ Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n 0) := by
  intro hTerminal
  cases L.no_third_sink hTerminal L.headroom_witness with
  | inl hAbsorbed =>
      exact L.nonzero_forbids_absorbed_static
        L.headroom_witness hAbsorbed
  | inr hProjected =>
      exact L.defect_forbids_projected_repair hTerminal hProjected

/-- Terminal defects are impossible when no-third-sink's projected branch
materializes an atom-pair realization. -/
theorem no_terminal_atom_projection_defect_of_materializing_no_third_sink
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (L :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n) :
    ¬ Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n 0) :=
  no_terminal_atom_projection_defect_of_no_third_sink
    (atomProjectionTerminalNoThirdSinkOfMaterializing L)

/-- Terminal defects are impossible when no-third-sink's projected branch is
read through a faithful projection functor. -/
theorem no_terminal_atom_projection_defect_of_projected_no_third_sink
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      AtomProjectionTerminalProjectedNoThirdSink
        Atomic SourceEvidence Residual n Projection) :
    ¬ Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n 0) :=
  no_terminal_atom_projection_defect_of_materializing_no_third_sink
    (atomProjectionTerminalMaterializingNoThirdSinkOfProjected L)

/-- Terminal defects are impossible when no-third-sink's projected branch only
asserts that the faithful partial projection is defined on the terminal
demand. -/
theorem no_terminal_atom_projection_defect_of_defined_no_third_sink
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      AtomProjectionTerminalDefinedNoThirdSink
        Atomic SourceEvidence Residual n Projection) :
    ¬ Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n 0) :=
  no_terminal_atom_projection_defect_of_projected_no_third_sink
    (atomProjectionTerminalProjectedNoThirdSinkOfDefined L)

/-- Terminal defects are impossible when projection failure in the projected
branch would force absorbed-static, and nonzero headroom rules absorption out.
-/
theorem no_terminal_atom_projection_defect_of_nonabsorbed_no_third_sink
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection) :
    ¬ Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n 0) :=
  no_terminal_atom_projection_defect_of_defined_no_third_sink
    (atomProjectionTerminalDefinedNoThirdSinkOfNonabsorbed L)

/-- Atom-projection defect finite-descent domain.

The `descend` field is the future hard transport / holonomy obligation.  It
must eventually be proved from source residual transport, not from endpoint
coverage. -/
structure AtomProjectionDefectDescentDomain
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat) where
  terminal_no_third_sink :
    AtomProjectionTerminalNoThirdSink
      Atomic SourceEvidence Residual n
  descend :
    ∀ {k : Nat},
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n k)

/-- Source-side one-step descent for repair demands.

This is the part that should come from representation/source residual
transport: a demand at shell `k + 1` has a source step to evidence at shell
`k`. -/
structure SourceDemandOneStepDescent
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat) where
  lowerEvidence :
    ∀ {k : Nat},
      RepRepairDemand SourceEvidence Residual n (k + 1) ->
        SourceEvidence
  step_to_lower :
    ∀ {k : Nat}
      (demand : RepRepairDemand SourceEvidence Residual n (k + 1)),
        Residual.step demand.evidence (lowerEvidence demand)

/-- Read a lower-shell repair demand from a source residual step. -/
def lowerDemandOfSourceStep
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (S : SourceDemandOneStepDescent SourceEvidence Residual n)
    (demand : RepRepairDemand SourceEvidence Residual n (k + 1)) :
    RepRepairDemand SourceEvidence Residual n k where
  evidence := S.lowerEvidence demand
  residual_eq := by
    have hstep :
        Residual.residualEnergy (S.lowerEvidence demand) + 1 =
          Residual.residualEnergy demand.evidence :=
      Residual.step_decreases_one (S.step_to_lower demand)
    have hsucc :
        Residual.residualEnergy (S.lowerEvidence demand) + 1 =
          k + 1 := by
      calc
        Residual.residualEnergy (S.lowerEvidence demand) + 1 =
            Residual.residualEnergy demand.evidence := hstep
        _ = k + 1 := demand.residual_eq
    exact Nat.succ.inj hsucc

/-- Iterate source one-step descent down to the terminal residual shell.

For a demand at shell `k`, this follows the source residual descent data `k`
times.  The result is still a source demand; no arithmetic endpoint search is
involved. -/
def terminalDemandOfSourceDescent
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (S : SourceDemandOneStepDescent SourceEvidence Residual n) :
    {k : Nat} ->
      RepRepairDemand SourceEvidence Residual n k ->
        RepRepairDemand SourceEvidence Residual n 0
  | 0, demand => demand
  | _ + 1, demand =>
      terminalDemandOfSourceDescent S
        (lowerDemandOfSourceStep S demand)

/-- Source-side projection-defined successor lift.

This is a source/projection alternative to arithmetic pair-energy successor
transport: projection defined at the lower repair demand lifts back to
projection defined at the current demand.  Future GT/crystal/branching
instances should justify this from projection compatibility with source
residual repair, not from endpoint coverage. -/
structure SourceProjectionDefinedSuccessorLift
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  projection_defined_lifts :
    ∀ {k : Nat}
      (demand : RepRepairDemand SourceEvidence Residual n (k + 1)),
        Projection.project
            (lowerDemandOfSourceStep source_descent demand).evidence ≠ none ->
          Projection.project demand.evidence ≠ none

/-- Projection-definedness is stable backward along one residual source step.

This is lower-level than `SourceProjectionDefinedSuccessorLift`: it is stated
directly on the source residual transport relation rather than on packaged
repair demands. -/
structure SourceProjectionStepCompatibility
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  projection_defined_lifts_along_step :
    ∀ {source target : SourceEvidence},
      Residual.step source target ->
        Projection.project target ≠ none ->
          Projection.project source ≠ none

/-- Residual repair steps are paths in the source feasible category.

This separates additive residual transport from the representation/source path
category.  Future GT/crystal/branching instances should prove this from their
native path/lowering relation. -/
structure ResidualStepSourcePathCompatibility
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence) where
  step_is_path :
    ∀ {source target : SourceEvidence},
      Residual.step source target ->
        Source.path source target

/-- Read a lower-shell feasible repair demand from a source residual step.

Feasibility is transported along the source path induced by the residual step;
this is the source-side reason the feasible demand stays in the representation
category during descent. -/
def lowerFeasibleDemandOfSourceStep
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (S : SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (demand :
      FeasibleRepRepairDemand SourceEvidence Residual Source n (k + 1)) :
    FeasibleRepRepairDemand SourceEvidence Residual Source n k where
  demand := lowerDemandOfSourceStep S demand.demand
  feasible :=
    Source.path_preserves_feasible
      (step_path.step_is_path (S.step_to_lower demand.demand))
      demand.feasible

/-- Iterate source one-step descent while preserving source feasibility. -/
def terminalFeasibleDemandOfSourceDescent
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (S : SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source) :
    {k : Nat} ->
      FeasibleRepRepairDemand SourceEvidence Residual Source n k ->
        FeasibleRepRepairDemand SourceEvidence Residual Source n 0
  | 0, demand => demand
  | _ + 1, demand =>
      terminalFeasibleDemandOfSourceDescent S step_path
        (lowerFeasibleDemandOfSourceStep S step_path demand)

/-- Source trace transport along feasible one-step residual descent.

This is deliberately separate from residual-energy descent: future source
instances must say how the source path / phase trace / sigma tag / producer
trace is carried to the lower repair demand instead of dropping that data as
metadata. -/
structure SourceRepairTraceDescent
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  lowerTrace :
    ∀ {k : Nat},
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n (k + 1) ->
        SourceRepairTrace SourcePath PhaseTrace SigmaTag ProducerTrace

/-- Read a lower-shell traced feasible repair demand from a trace-preserving
source residual step. -/
def lowerTracedFeasibleDemandOfSourceStep
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (S : SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (Trace :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n (k + 1)) :
    TracedFeasibleRepRepairDemand
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n k where
  demand :=
    lowerFeasibleDemandOfSourceStep
      S step_path demand.demand
  trace := Trace.lowerTrace demand

/-- Iterate source one-step descent down to the terminal residual shell while
preserving source trace data. -/
def terminalTracedFeasibleDemandOfSourceDescent
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (S : SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (Trace :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n) :
    {k : Nat} ->
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k ->
        TracedFeasibleRepRepairDemand
          SourcePath PhaseTrace SigmaTag ProducerTrace
          SourceEvidence Residual Source n 0
  | 0, demand => demand
  | _ + 1, demand =>
      terminalTracedFeasibleDemandOfSourceDescent
        S step_path Trace
        (lowerTracedFeasibleDemandOfSourceStep
          S step_path Trace demand)

/-- Projection-definedness is stable backward along source paths. -/
structure SourceProjectionPathCompatibility
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  projection_defined_lifts_along_path :
    ∀ {source target : SourceEvidence},
      Source.path source target ->
        Projection.project target ≠ none ->
          Projection.project source ≠ none

/-- Code-projection definedness is stable backward along source paths.

This is the code-level analogue of `SourceProjectionPathCompatibility`: source
paths first preserve raw endpoint-code definedness; atom-pair materialization
is obtained later from atomic endpoint certification. -/
structure SourceCodeProjectionPathCompatibility
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual) where
  code_projection_defined_lifts_along_path :
    ∀ {source target : SourceEvidence},
      Source.path source target ->
        Projection.codeProjection.projectCode target ≠ none ->
          Projection.codeProjection.projectCode source ≠ none

/-- A code-projection path compatibility plus a direct-readout certificate
induces the older atom-projection path compatibility. -/
theorem sourceProjectionPathCompatibilityOfCodeProjectionReadout
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {CodeProjection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (readout :
      AtomicCodeProjectionDirectReadout
        Atomic SourceEvidence Residual n CodeProjection)
    (path_compat :
      SourceCodeProjectionPathCompatibility
        Atomic SourceEvidence Residual n Source CodeProjection) :
    SourceProjectionPathCompatibility
      Atomic SourceEvidence Residual n Source
      readout.atomProjection := by
  refine { projection_defined_lifts_along_path := ?_ }
  intro source target hPath hTargetDefined
  have hTargetCodeDefined :
      CodeProjection.codeProjection.projectCode target ≠ none :=
    (readout.atom_projection_defined_iff_code_projection_defined target).mp
      hTargetDefined
  have hSourceCodeDefined :
      CodeProjection.codeProjection.projectCode source ≠ none :=
    path_compat.code_projection_defined_lifts_along_path
      hPath hTargetCodeDefined
  exact
    (readout.atom_projection_defined_iff_code_projection_defined source).mpr
      hSourceCodeDefined

/-- Source-path projection compatibility plus residual-step path readout
induces step-level projection compatibility. -/
theorem sourceProjectionStepCompatibilityOfPathCompatibility
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (path_compat :
      SourceProjectionPathCompatibility
        Atomic SourceEvidence Residual n Source Projection) :
    SourceProjectionStepCompatibility
      Atomic SourceEvidence Residual n Projection := by
  refine { projection_defined_lifts_along_step := ?_ }
  intro source target hStep hTargetDefined
  exact
    path_compat.projection_defined_lifts_along_path
      (step_path.step_is_path hStep)
      hTargetDefined

/-- Step-level source/projection compatibility induces the demand-level
projection-defined successor lift. -/
def sourceProjectionDefinedSuccessorLiftOfStepCompatibility
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (source_descent :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (compat :
      SourceProjectionStepCompatibility
        Atomic SourceEvidence Residual n Projection) :
    SourceProjectionDefinedSuccessorLift
      Atomic SourceEvidence Residual n Projection where
  source_descent := source_descent
  projection_defined_lifts := by
    intro k demand hLowerDefined
    exact
      compat.projection_defined_lifts_along_step
        (source_descent.step_to_lower demand)
        hLowerDefined

/-- If terminal projection is defined along the source descent trail, then the
original demand's projection is defined. -/
theorem projection_defined_of_terminal_source_descent
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      SourceProjectionDefinedSuccessorLift
        Atomic SourceEvidence Residual n Projection) :
    ∀ {k : Nat}
      (demand : RepRepairDemand SourceEvidence Residual n k),
        Projection.project
            (terminalDemandOfSourceDescent L.source_descent demand).evidence ≠
          none ->
        Projection.project demand.evidence ≠ none := by
  intro k
  induction k with
  | zero =>
      intro demand hTerminal
      exact hTerminal
  | succ k ih =>
      intro demand hTerminal
      exact
        L.projection_defined_lifts demand
          (ih
            (lowerDemandOfSourceStep L.source_descent demand)
            hTerminal)

/-- If terminal endpoint-code projection is defined along the source descent
trail, then the original demand's endpoint-code projection is defined.

This is the code-level version of `projection_defined_of_terminal_source_descent`.
It does not require atom-pair projection to exist as a primitive functor. -/
theorem code_projection_defined_of_terminal_source_descent
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (source_descent :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (path_compat :
      SourceCodeProjectionPathCompatibility
        Atomic SourceEvidence Residual n Source Projection) :
    ∀ {k : Nat}
      (demand : RepRepairDemand SourceEvidence Residual n k),
        Projection.codeProjection.projectCode
            (terminalDemandOfSourceDescent source_descent demand).evidence ≠
          none ->
        Projection.codeProjection.projectCode demand.evidence ≠ none := by
  intro k
  induction k with
  | zero =>
      intro demand hTerminal
      exact hTerminal
  | succ k ih =>
      intro demand hTerminal
      have hLowerDefined :
          Projection.codeProjection.projectCode
              (lowerDemandOfSourceStep source_descent demand).evidence ≠
            none :=
        ih (lowerDemandOfSourceStep source_descent demand) hTerminal
      exact
        path_compat.code_projection_defined_lifts_along_path
          (step_path.step_is_path (source_descent.step_to_lower demand))
          hLowerDefined

/-- If terminal projection is defined along the traced source descent trail,
then the original traced demand's projection is defined.

This keeps sourcePath / phaseTrace / sigmaTag / producerTrace inside the
transport socket instead of dropping them before the terminal nonabsorption
law is applied. -/
theorem projection_defined_of_terminal_traced_source_descent
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (source_descent :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (path_compat :
      SourceProjectionPathCompatibility
        Atomic SourceEvidence Residual n Source Projection) :
    ∀ {k : Nat}
      (demand :
        TracedFeasibleRepRepairDemand
          SourcePath PhaseTrace SigmaTag ProducerTrace
          SourceEvidence Residual Source n k),
        Projection.project
            (terminalTracedFeasibleDemandOfSourceDescent
              source_descent step_path trace_descent demand).demand.demand.evidence
          ≠ none ->
        Projection.project demand.demand.demand.evidence ≠ none := by
  intro k
  induction k with
  | zero =>
      intro demand hTerminal
      exact hTerminal
  | succ k ih =>
      intro demand hTerminal
      have hLowerDefined :
          Projection.project
              (lowerTracedFeasibleDemandOfSourceStep
                source_descent step_path trace_descent demand).demand.demand.evidence
            ≠ none :=
        ih
          (lowerTracedFeasibleDemandOfSourceStep
            source_descent step_path trace_descent demand)
          hTerminal
      exact
        path_compat.projection_defined_lifts_along_path
          (step_path.step_is_path
            (source_descent.step_to_lower demand.demand.demand))
          hLowerDefined

/-- Code-projection version of
`projection_defined_of_terminal_traced_source_descent`. -/
theorem code_projection_defined_of_terminal_traced_source_descent
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (source_descent :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (path_compat :
      SourceCodeProjectionPathCompatibility
        Atomic SourceEvidence Residual n Source Projection) :
    ∀ {k : Nat}
      (demand :
        TracedFeasibleRepRepairDemand
          SourcePath PhaseTrace SigmaTag ProducerTrace
          SourceEvidence Residual Source n k),
        Projection.codeProjection.projectCode
            (terminalTracedFeasibleDemandOfSourceDescent
              source_descent step_path trace_descent demand).demand.demand.evidence
          ≠ none ->
        Projection.codeProjection.projectCode demand.demand.demand.evidence ≠
          none := by
  intro k
  induction k with
  | zero =>
      intro demand hTerminal
      exact hTerminal
  | succ k ih =>
      intro demand hTerminal
      have hLowerDefined :
          Projection.codeProjection.projectCode
              (lowerTracedFeasibleDemandOfSourceStep
                source_descent step_path trace_descent demand).demand.demand.evidence
            ≠ none :=
        ih
          (lowerTracedFeasibleDemandOfSourceStep
            source_descent step_path trace_descent demand)
          hTerminal
      exact
        path_compat.code_projection_defined_lifts_along_path
          (step_path.step_is_path
            (source_descent.step_to_lower demand.demand.demand))
          hLowerDefined

/-- Terminal projection definedness plus source projection-defined successor
lift gives an atom-pair realization at the original demand's shell. -/
theorem atom_pair_realization_of_terminal_source_projection_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      SourceProjectionDefinedSuccessorLift
        Atomic SourceEvidence Residual n Projection)
    (demand : RepRepairDemand SourceEvidence Residual n k)
    (hTerminalDefined :
      Projection.project
          (terminalDemandOfSourceDescent L.source_descent demand).evidence ≠
        none) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  atom_pair_realization_of_defined_projected_demand
    Projection
    demand
    (projection_defined_of_terminal_source_descent
      L demand hTerminalDefined)

/-- Demand-level defect exclusion from terminal projection definedness and
source projection-defined successor lift. -/
theorem not_defect_of_terminal_source_projection_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      SourceProjectionDefinedSuccessorLift
        Atomic SourceEvidence Residual n Projection)
    (demand : RepRepairDemand SourceEvidence Residual n k)
    (hTerminalDefined :
      Projection.project
          (terminalDemandOfSourceDescent L.source_descent demand).evidence ≠
        none) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  not_defect_of_atom_realization
    (atom_pair_realization_of_terminal_source_projection_lift
      L demand hTerminalDefined)

/-- Terminal nonabsorbedness plus source projection-defined successor lift
gives an atom-pair realization at the original demand's shell. -/
theorem atom_pair_realization_of_nonabsorbed_terminal_source_projection_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    {absorbed_static : Prop}
    (L :
      SourceProjectionDefinedSuccessorLift
        Atomic SourceEvidence Residual n Projection)
    (demand : RepRepairDemand SourceEvidence Residual n k)
    (hNotAbsorbed : ¬ absorbed_static)
    (hUndefinedAbsorbs :
      Projection.project
          (terminalDemandOfSourceDescent L.source_descent demand).evidence =
        none ->
          absorbed_static) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  atom_pair_realization_of_terminal_source_projection_lift
    L demand
    (fun hNone => hNotAbsorbed (hUndefinedAbsorbs hNone))

/-- Uniform source/projection nonabsorbed lift domain.

This packages the source-side route for all demands in a fixed fiber: descend
to the terminal source demand, rule out terminal projection silence by showing
it would be absorbed, then lift projection-definedness back to the original
demand. -/
structure SourceProjectionNonabsorbedLiftDomain
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  projection_lift :
    SourceProjectionDefinedSuccessorLift
      Atomic SourceEvidence Residual n Projection
  absorbed_static : Prop
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  terminal_projection_undefined_absorbs :
    ∀ {k : Nat}
      (demand : RepRepairDemand SourceEvidence Residual n k),
        Projection.project
            (terminalDemandOfSourceDescent
              projection_lift.source_descent demand).evidence =
        none ->
            absorbed_static

/-- Uniform source/projection nonabsorbed lift domain stated at the residual
step level.  This is the preferred interface for a concrete source category:
prove projection-definedness stability along each source step, then the
demand-level lift is derived. -/
structure SourceProjectionStepNonabsorbedLiftDomain
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_compatibility :
    SourceProjectionStepCompatibility
      Atomic SourceEvidence Residual n Projection
  absorbed_static : Prop
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  terminal_projection_undefined_absorbs :
    ∀ {k : Nat}
      (demand : RepRepairDemand SourceEvidence Residual n k),
        Projection.project
            (terminalDemandOfSourceDescent source_descent demand).evidence =
        none ->
            absorbed_static

/-- Uniform source/projection nonabsorbed lift domain stated through the
source feasible path category.  This is the lowest current source-side
interface: residual steps become source paths, and projection-definedness is
stable backward along those paths. -/
structure SourceProjectionPathNonabsorbedLiftDomain
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  path_compatibility :
    SourceProjectionPathCompatibility
      Atomic SourceEvidence Residual n Source Projection
  absorbed_static : Prop
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  terminal_projection_undefined_absorbs :
    ∀ {k : Nat}
      (demand : RepRepairDemand SourceEvidence Residual n k),
        Projection.project
            (terminalDemandOfSourceDescent source_descent demand).evidence =
          none ->
            absorbed_static

/-- Feasible-scoped source/projection nonabsorbed lift domain.

Unlike `SourceProjectionPathNonabsorbedLiftDomain`, the terminal absorption
law is required only for feasible source repair demands.  This is the better
interface for representation categories where arbitrary residual evidence
need not be a legitimate active demand. -/
structure FeasibleSourceProjectionPathNonabsorbedLiftDomain
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  path_compatibility :
    SourceProjectionPathCompatibility
      Atomic SourceEvidence Residual n Source Projection
  absorbed_static : Prop
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  terminal_projection_undefined_absorbs :
    ∀ {k : Nat}
      (demand : FeasibleRepRepairDemand SourceEvidence Residual Source n k),
        Projection.project
            (terminalDemandOfSourceDescent
              source_descent demand.demand).evidence =
          none ->
            absorbed_static

/-- Feasible source/code-projection nonabsorbed lift domain.

This is the more granular code-projection route: source paths lift
definedness of raw endpoint-code projection; multiplicative atomicity is then
certified by `AtomicEndpointCodeProjection` before forming an atom pair. -/
structure FeasibleSourceCodeProjectionPathNonabsorbedLiftDomain
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  path_compatibility :
    SourceCodeProjectionPathCompatibility
      Atomic SourceEvidence Residual n Source Projection
  absorbed_static : Prop
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  terminal_code_projection_undefined_absorbs :
    ∀ {k : Nat}
      (demand : FeasibleRepRepairDemand SourceEvidence Residual Source n k),
        Projection.codeProjection.projectCode
            (terminalDemandOfSourceDescent
              source_descent demand.demand).evidence =
          none ->
            absorbed_static

/-- Traced feasible source/projection nonabsorbed lift domain.

This is the traced analogue of
`FeasibleSourceProjectionPathNonabsorbedLiftDomain`: terminal projection
silence is judged on the trace-preserving terminal descent of the active
source demand, so the sourcePath / phaseTrace / sigmaTag / producerTrace
payload remains part of the mechanism. -/
structure TracedFeasibleSourceProjectionPathNonabsorbedLiftDomain
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  trace_descent :
    SourceRepairTraceDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n
  path_compatibility :
    SourceProjectionPathCompatibility
      Atomic SourceEvidence Residual n Source Projection
  absorbed_static : Prop
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  terminal_projection_undefined_absorbs :
    ∀ {k : Nat}
      (demand :
        TracedFeasibleRepRepairDemand
          SourcePath PhaseTrace SigmaTag ProducerTrace
          SourceEvidence Residual Source n k),
        Projection.project
            (terminalTracedFeasibleDemandOfSourceDescent
              source_descent step_path trace_descent demand).demand.demand.evidence =
          none ->
            absorbed_static

/-- Traced feasible source/code-projection nonabsorbed lift domain.

The source path transports raw endpoint-code definedness; atom-pair
materialization remains delegated to endpoint atomicity certification. -/
structure TracedFeasibleSourceCodeProjectionPathNonabsorbedLiftDomain
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  trace_descent :
    SourceRepairTraceDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n
  path_compatibility :
    SourceCodeProjectionPathCompatibility
      Atomic SourceEvidence Residual n Source Projection
  absorbed_static : Prop
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  terminal_code_projection_undefined_absorbs :
    ∀ {k : Nat}
      (demand :
        TracedFeasibleRepRepairDemand
          SourcePath PhaseTrace SigmaTag ProducerTrace
          SourceEvidence Residual Source n k),
        Projection.codeProjection.projectCode
            (terminalTracedFeasibleDemandOfSourceDescent
              source_descent step_path trace_descent demand).demand.demand.evidence =
          none ->
            absorbed_static

/-- A feasible code-projection nonabsorbed domain plus direct readout induces
the older feasible atom-projection nonabsorbed domain. -/
def feasibleSourceProjectionPathNonabsorbedLiftDomainOfCodeProjectionReadout
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {CodeProjection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (readout :
      AtomicCodeProjectionDirectReadout
        Atomic SourceEvidence Residual n CodeProjection)
    (D :
      FeasibleSourceCodeProjectionPathNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Source CodeProjection) :
    FeasibleSourceProjectionPathNonabsorbedLiftDomain
      Atomic SourceEvidence Residual n Source readout.atomProjection where
  source_descent := D.source_descent
  step_path := D.step_path
  path_compatibility :=
    sourceProjectionPathCompatibilityOfCodeProjectionReadout
      readout D.path_compatibility
  absorbed_static := D.absorbed_static
  headroom_nonzero := D.headroom_nonzero
  headroom_witness := D.headroom_witness
  nonzero_forbids_absorbed_static :=
    D.nonzero_forbids_absorbed_static
  terminal_projection_undefined_absorbs := by
    intro k demand hAtomNone
    exact
      D.terminal_code_projection_undefined_absorbs demand
        ((readout.atom_projection_none_iff_code_projection_none
          (terminalDemandOfSourceDescent
            D.source_descent demand.demand).evidence).mp hAtomNone)

/-- Step-level source/projection data induces the demand-level nonabsorbed
lift domain. -/
def sourceProjectionNonabsorbedLiftDomainOfStepCompatibility
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (D :
      SourceProjectionStepNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Projection) :
    SourceProjectionNonabsorbedLiftDomain
      Atomic SourceEvidence Residual n Projection where
  projection_lift :=
    sourceProjectionDefinedSuccessorLiftOfStepCompatibility
      D.source_descent D.step_compatibility
  absorbed_static := D.absorbed_static
  headroom_nonzero := D.headroom_nonzero
  headroom_witness := D.headroom_witness
  nonzero_forbids_absorbed_static :=
    D.nonzero_forbids_absorbed_static
  terminal_projection_undefined_absorbs :=
    D.terminal_projection_undefined_absorbs

/-- Path-level source/projection data induces the step-level nonabsorbed lift
domain. -/
def sourceProjectionStepNonabsorbedLiftDomainOfPathCompatibility
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (D :
      SourceProjectionPathNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Source Projection) :
    SourceProjectionStepNonabsorbedLiftDomain
      Atomic SourceEvidence Residual n Projection where
  source_descent := D.source_descent
  step_compatibility :=
    sourceProjectionStepCompatibilityOfPathCompatibility
      D.step_path D.path_compatibility
  absorbed_static := D.absorbed_static
  headroom_nonzero := D.headroom_nonzero
  headroom_witness := D.headroom_witness
  nonzero_forbids_absorbed_static :=
    D.nonzero_forbids_absorbed_static
  terminal_projection_undefined_absorbs :=
    D.terminal_projection_undefined_absorbs

/-- In a uniform source/projection nonabsorbed lift domain, every repair demand
has an atom-pair realization at its residual shell. -/
theorem atom_pair_realization_of_source_projection_nonabsorbed_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (D :
      SourceProjectionNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Projection)
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  atom_pair_realization_of_nonabsorbed_terminal_source_projection_lift
    D.projection_lift
    demand
    (D.nonzero_forbids_absorbed_static D.headroom_witness)
    (D.terminal_projection_undefined_absorbs demand)

/-- The same source/projection domain rules out a defect for any concrete
repair demand. -/
theorem not_defect_of_source_projection_nonabsorbed_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (D :
      SourceProjectionNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Projection)
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  not_defect_of_atom_realization
    (atom_pair_realization_of_source_projection_nonabsorbed_lift
      D demand)

/-- Step-level source/projection nonabsorbed lift gives realization for every
repair demand. -/
theorem atom_pair_realization_of_source_projection_step_nonabsorbed_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (D :
      SourceProjectionStepNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Projection)
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  atom_pair_realization_of_source_projection_nonabsorbed_lift
    (sourceProjectionNonabsorbedLiftDomainOfStepCompatibility D)
    demand

/-- Step-level source/projection nonabsorbed lift rules out a concrete
projection defect. -/
theorem not_defect_of_source_projection_step_nonabsorbed_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (D :
      SourceProjectionStepNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Projection)
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  not_defect_of_source_projection_nonabsorbed_lift
    (sourceProjectionNonabsorbedLiftDomainOfStepCompatibility D)
    demand

/-- Path-level source/projection nonabsorbed lift gives realization for every
repair demand. -/
theorem atom_pair_realization_of_source_projection_path_nonabsorbed_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (D :
      SourceProjectionPathNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Source Projection)
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  atom_pair_realization_of_source_projection_step_nonabsorbed_lift
    (sourceProjectionStepNonabsorbedLiftDomainOfPathCompatibility D)
    demand

/-- Path-level source/projection nonabsorbed lift rules out a concrete
projection defect. -/
theorem not_defect_of_source_projection_path_nonabsorbed_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (D :
      SourceProjectionPathNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Source Projection)
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  not_defect_of_source_projection_step_nonabsorbed_lift
    (sourceProjectionStepNonabsorbedLiftDomainOfPathCompatibility D)
    demand

/-- Feasible path-level source/projection nonabsorbed lift gives realization
for every feasible repair demand. -/
theorem atom_pair_realization_of_feasible_source_projection_path_nonabsorbed_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (D :
      FeasibleSourceProjectionPathNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Source Projection)
    (demand :
      FeasibleRepRepairDemand SourceEvidence Residual Source n k) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k := by
  let L :
      SourceProjectionDefinedSuccessorLift
        Atomic SourceEvidence Residual n Projection :=
    sourceProjectionDefinedSuccessorLiftOfStepCompatibility
      D.source_descent
      (sourceProjectionStepCompatibilityOfPathCompatibility
        D.step_path D.path_compatibility)
  exact
    atom_pair_realization_of_nonabsorbed_terminal_source_projection_lift
      L
      demand.demand
      (D.nonzero_forbids_absorbed_static D.headroom_witness)
      (D.terminal_projection_undefined_absorbs demand)

/-- Feasible path-level source/projection nonabsorbed lift rules out a
feasible projection defect. -/
theorem not_feasible_defect_of_source_projection_path_nonabsorbed_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (D :
      FeasibleSourceProjectionPathNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Source Projection)
    (demand :
      FeasibleRepRepairDemand SourceEvidence Residual Source n k) :
    ¬ Nonempty
      (FeasibleAtomProjectionDefect
        Atomic SourceEvidence Residual Source n k) :=
  not_feasible_defect_of_atom_realization
    (atom_pair_realization_of_feasible_source_projection_path_nonabsorbed_lift
      D demand)

/-- Feasible source/code-projection nonabsorbed lift gives atom-pair
realization for every feasible repair demand.

The projection branch is deliberately code-level: Lean first proves raw
endpoint-code projection is defined, then uses endpoint atomicity
certification to build the arithmetic atom pair. -/
theorem atom_pair_realization_of_feasible_source_code_projection_path_nonabsorbed_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (D :
      FeasibleSourceCodeProjectionPathNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Source Projection)
    (demand :
      FeasibleRepRepairDemand SourceEvidence Residual Source n k) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k := by
  have hNotAbsorbed : ¬ D.absorbed_static :=
    D.nonzero_forbids_absorbed_static D.headroom_witness
  have hTerminalDefined :
      Projection.codeProjection.projectCode
          (terminalDemandOfSourceDescent
            D.source_descent demand.demand).evidence ≠
        none := by
    intro hNone
    exact hNotAbsorbed
      (D.terminal_code_projection_undefined_absorbs demand hNone)
  have hDefined :
      Projection.codeProjection.projectCode demand.demand.evidence ≠ none :=
    code_projection_defined_of_terminal_source_descent
      D.source_descent D.step_path D.path_compatibility
      demand.demand hTerminalDefined
  exact
    atom_pair_realization_of_atomic_code_defined_demand
      Projection demand.demand hDefined

/-- Feasible source/code-projection nonabsorbed lift rules out a feasible
projection defect. -/
theorem not_feasible_defect_of_source_code_projection_path_nonabsorbed_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (D :
      FeasibleSourceCodeProjectionPathNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Source Projection)
    (demand :
      FeasibleRepRepairDemand SourceEvidence Residual Source n k) :
    ¬ Nonempty
      (FeasibleAtomProjectionDefect
        Atomic SourceEvidence Residual Source n k) :=
  not_feasible_defect_of_atom_realization
    (atom_pair_realization_of_feasible_source_code_projection_path_nonabsorbed_lift
      D demand)

/-- Traced feasible source/projection nonabsorbed lift gives an atom-pair
realization for the traced active repair demand. -/
theorem atom_pair_realization_of_traced_feasible_source_projection_path_nonabsorbed_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (D :
      TracedFeasibleSourceProjectionPathNonabsorbedLiftDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k := by
  have hNotAbsorbed : ¬ D.absorbed_static :=
    D.nonzero_forbids_absorbed_static D.headroom_witness
  have hTerminalDefined :
      Projection.project
          (terminalTracedFeasibleDemandOfSourceDescent
            D.source_descent D.step_path D.trace_descent demand).demand.demand.evidence
        ≠ none := by
    intro hNone
    exact hNotAbsorbed
      (D.terminal_projection_undefined_absorbs demand hNone)
  have hDefined :
      Projection.project demand.demand.demand.evidence ≠ none :=
    projection_defined_of_terminal_traced_source_descent
      D.source_descent D.step_path D.trace_descent D.path_compatibility
      demand hTerminalDefined
  exact
    atom_pair_realization_of_defined_projected_demand
      Projection demand.demand.demand hDefined

/-- Traced feasible source/projection nonabsorbed lift rules out traced
feasible projection defects. -/
theorem not_traced_feasible_defect_of_source_projection_path_nonabsorbed_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (D :
      TracedFeasibleSourceProjectionPathNonabsorbedLiftDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) :=
  not_traced_feasible_defect_of_atom_realization
    (atom_pair_realization_of_traced_feasible_source_projection_path_nonabsorbed_lift
      D demand)

/-- Traced feasible source/code-projection nonabsorbed lift gives atom-pair
realization for the traced active repair demand. -/
theorem atom_pair_realization_of_traced_feasible_source_code_projection_path_nonabsorbed_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (D :
      TracedFeasibleSourceCodeProjectionPathNonabsorbedLiftDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k := by
  have hNotAbsorbed : ¬ D.absorbed_static :=
    D.nonzero_forbids_absorbed_static D.headroom_witness
  have hTerminalDefined :
      Projection.codeProjection.projectCode
          (terminalTracedFeasibleDemandOfSourceDescent
            D.source_descent D.step_path D.trace_descent demand).demand.demand.evidence
        ≠ none := by
    intro hNone
    exact hNotAbsorbed
      (D.terminal_code_projection_undefined_absorbs demand hNone)
  have hDefined :
      Projection.codeProjection.projectCode demand.demand.demand.evidence ≠
        none :=
    code_projection_defined_of_terminal_traced_source_descent
      D.source_descent D.step_path D.trace_descent D.path_compatibility
      demand hTerminalDefined
  exact
    atom_pair_realization_of_atomic_code_defined_demand
      Projection demand.demand.demand hDefined

/-- Traced feasible source/code-projection nonabsorbed lift rules out traced
feasible projection defects. -/
theorem not_traced_feasible_defect_of_source_code_projection_path_nonabsorbed_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (D :
      TracedFeasibleSourceCodeProjectionPathNonabsorbedLiftDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual n Source Projection)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) :=
  not_traced_feasible_defect_of_atom_realization
    (atom_pair_realization_of_traced_feasible_source_code_projection_path_nonabsorbed_lift
      D demand)

/-- A path-level source/projection nonabsorbed lift domain generates the
previous discharge-law socket.

This is the important bridge back to `StableTransportAtomProjectionDomain`:
the old `realization_of_demand` field is no longer an independent witness
return.  It is derived from source paths, projection-definedness stability,
terminal nonabsorption, and faithful projection readout. -/
def atomProjectionDefectDischargeLawOfSourceProjectionPathNonabsorbedLift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (D :
      SourceProjectionPathNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Source Projection) :
    AtomProjectionDefectDischargeLaw
      Atomic SourceEvidence n Residual Source Projection where
  defect_propagates_or_discharges := True
  finite_descent_or_holonomy_bound := True
  no_third_sink_or_naked_terminal_defect := True
  realization_of_demand := by
    intro k demand
    exact
      atom_pair_realization_of_source_projection_path_nonabsorbed_lift
        D demand

/-- A feasible path-level source/projection nonabsorbed lift domain generates
the feasible-scoped discharge-law socket. -/
def feasibleAtomProjectionDefectDischargeLawOfSourceProjectionPathNonabsorbedLift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (D :
      FeasibleSourceProjectionPathNonabsorbedLiftDomain
        Atomic SourceEvidence Residual n Source Projection) :
    FeasibleAtomProjectionDefectDischargeLaw
      Atomic SourceEvidence n Residual Source Projection where
  defect_propagates_or_discharges := True
  finite_descent_or_holonomy_bound := True
  no_third_sink_or_naked_terminal_defect := True
  realization_of_feasible_demand := by
    intro k demand
    exact
      atom_pair_realization_of_feasible_source_projection_path_nonabsorbed_lift
        D demand

/-- Stable transport/projection domain whose discharge law is generated from
path-level source/projection nonabsorbed lift, rather than supplied as a
witness-return field. -/
structure SourcePathStableTransportAtomProjectionDomain
    (Atomic : Nat -> Prop) (SourceEvidence : Type u) (n : Nat) where
  multiplicative_atoms : MultiplicativeAtomFactorizationCategory Atomic
  residual_transport : AdditiveResidualTransportCategory SourceEvidence
  source_category : RepresentationFeasibleCategory SourceEvidence
  projection_functor :
    FaithfulAtomProjectionFunctor Atomic SourceEvidence n residual_transport
  source_path_nonabsorbed :
    SourceProjectionPathNonabsorbedLiftDomain
      Atomic SourceEvidence residual_transport n source_category
      projection_functor

/-- Feasible stable transport/projection domain whose discharge law is
generated from feasible path-level source/projection nonabsorbed lift. -/
structure FeasibleSourcePathStableTransportAtomProjectionDomain
    (Atomic : Nat -> Prop) (SourceEvidence : Type u) (n : Nat) where
  multiplicative_atoms : MultiplicativeAtomFactorizationCategory Atomic
  residual_transport : AdditiveResidualTransportCategory SourceEvidence
  source_category : RepresentationFeasibleCategory SourceEvidence
  projection_functor :
    FaithfulAtomProjectionFunctor Atomic SourceEvidence n residual_transport
  source_path_nonabsorbed :
    FeasibleSourceProjectionPathNonabsorbedLiftDomain
      Atomic SourceEvidence residual_transport n source_category
      projection_functor

/-- Feasible stable domain generated by raw endpoint-code projection plus
endpoint atomicity certification.

This keeps the code-projection bridge explicit: the source side provides raw
endpoint codes, and `AtomicEndpointCodeProjection` certifies that the projected
codes are multiplicative atoms before they become `ArithmeticAtomPair`
objects. -/
structure FeasibleSourceCodePathStableAtomProjectionDomain
    (Atomic : Nat -> Prop) (SourceEvidence : Type u) (n : Nat) where
  multiplicative_atoms : MultiplicativeAtomFactorizationCategory Atomic
  residual_transport : AdditiveResidualTransportCategory SourceEvidence
  source_category : RepresentationFeasibleCategory SourceEvidence
  code_projection :
    AtomicEndpointCodeProjection Atomic SourceEvidence n residual_transport
  source_code_path_nonabsorbed :
    FeasibleSourceCodeProjectionPathNonabsorbedLiftDomain
      Atomic SourceEvidence residual_transport n source_category
      code_projection

/-- With an explicit direct-readout certificate, a code-projection generated
stable domain can be viewed as an older direct atom-projection stable domain.
-/
def feasibleSourcePathStableTransportAtomProjectionDomainOfCodeProjectionReadout
    {Atomic : Nat -> Prop} {SourceEvidence : Type u} {n : Nat}
    (D :
      FeasibleSourceCodePathStableAtomProjectionDomain
        Atomic SourceEvidence n)
    (readout :
      AtomicCodeProjectionDirectReadout
        Atomic SourceEvidence D.residual_transport n D.code_projection) :
    FeasibleSourcePathStableTransportAtomProjectionDomain
      Atomic SourceEvidence n where
  multiplicative_atoms := D.multiplicative_atoms
  residual_transport := D.residual_transport
  source_category := D.source_category
  projection_functor := readout.atomProjection
  source_path_nonabsorbed :=
    feasibleSourceProjectionPathNonabsorbedLiftDomainOfCodeProjectionReadout
      readout D.source_code_path_nonabsorbed

/-- Convert the source-path generated domain to the original stable domain
socket by deriving the discharge law. -/
def stableTransportAtomProjectionDomainOfSourcePath
    {Atomic : Nat -> Prop} {SourceEvidence : Type u} {n : Nat}
    (D :
      SourcePathStableTransportAtomProjectionDomain
        Atomic SourceEvidence n) :
    StableTransportAtomProjectionDomain Atomic SourceEvidence n where
  multiplicative_atoms := D.multiplicative_atoms
  residual_transport := D.residual_transport
  source_category := D.source_category
  projection_functor := D.projection_functor
  discharge_law :=
    atomProjectionDefectDischargeLawOfSourceProjectionPathNonabsorbedLift
      D.source_path_nonabsorbed

/-- Convert the feasible source-path generated domain to the feasible stable
domain socket by deriving the feasible discharge law. -/
def feasibleStableTransportAtomProjectionDomainOfSourcePath
    {Atomic : Nat -> Prop} {SourceEvidence : Type u} {n : Nat}
    (D :
      FeasibleSourcePathStableTransportAtomProjectionDomain
        Atomic SourceEvidence n) :
    FeasibleStableTransportAtomProjectionDomain Atomic SourceEvidence n where
  multiplicative_atoms := D.multiplicative_atoms
  residual_transport := D.residual_transport
  source_category := D.source_category
  projection_functor := D.projection_functor
  discharge_law :=
    feasibleAtomProjectionDefectDischargeLawOfSourceProjectionPathNonabsorbedLift
      D.source_path_nonabsorbed

/-- Core stable-domain theorem specialized to source-path generated discharge.
-/
theorem no_stable_atom_projection_defect_of_source_path_domain
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {n k : Nat}
    (D :
      SourcePathStableTransportAtomProjectionDomain
        Atomic SourceEvidence n) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence
        D.residual_transport n k) :=
  no_stable_atom_projection_defect
    (stableTransportAtomProjectionDomainOfSourcePath D)

/-- Feasible stable-domain theorem specialized to feasible source-path
generated discharge. -/
theorem no_feasible_atom_projection_defect_of_source_path_domain
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {n k : Nat}
    (D :
      FeasibleSourcePathStableTransportAtomProjectionDomain
        Atomic SourceEvidence n) :
    ¬ Nonempty
      (FeasibleAtomProjectionDefect
        Atomic SourceEvidence D.residual_transport D.source_category n k) :=
  no_feasible_stable_atom_projection_defect
    (feasibleStableTransportAtomProjectionDomainOfSourcePath D)

/-- Feasible source-path stable domains also return multiplicative
factorization readout for the realized endpoints. -/
theorem factorized_atom_pair_realization_of_feasible_source_path_domain
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {n k : Nat}
    (D :
      FeasibleSourcePathStableTransportAtomProjectionDomain
        Atomic SourceEvidence n)
    (demand :
      FeasibleRepRepairDemand
        SourceEvidence D.residual_transport D.source_category n k) :
    FactorizedAtomPairRealization
      Atomic D.multiplicative_atoms n k := by
  rcases
    atom_pair_realization_of_feasible_source_projection_path_nonabsorbed_lift
      D.source_path_nonabsorbed demand with
  ⟨p, hEnergy⟩
  exact
    factorizedAtomPairRealizationOfPair
      D.multiplicative_atoms p hEnergy

/-- Code-projection generated feasible stable domains rule out feasible
atom-projection defects. -/
theorem no_feasible_atom_projection_defect_of_source_code_path_domain
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {n k : Nat}
    (D :
      FeasibleSourceCodePathStableAtomProjectionDomain
        Atomic SourceEvidence n) :
    ¬ Nonempty
      (FeasibleAtomProjectionDefect
        Atomic SourceEvidence D.residual_transport D.source_category n k) := by
  intro hdefect
  rcases hdefect with ⟨defect⟩
  exact defect.noAtomRealization
    (atom_pair_realization_of_feasible_source_code_projection_path_nonabsorbed_lift
      D.source_code_path_nonabsorbed defect.demand)

/-- Code-projection generated feasible stable domains return multiplicative
factorization readout for the realized endpoints. -/
theorem factorized_atom_pair_realization_of_feasible_source_code_path_domain
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {n k : Nat}
    (D :
      FeasibleSourceCodePathStableAtomProjectionDomain
        Atomic SourceEvidence n)
    (demand :
      FeasibleRepRepairDemand
        SourceEvidence D.residual_transport D.source_category n k) :
    FactorizedAtomPairRealization
      Atomic D.multiplicative_atoms n k := by
  rcases
    atom_pair_realization_of_feasible_source_code_projection_path_nonabsorbed_lift
      D.source_code_path_nonabsorbed demand with
  ⟨p, hEnergy⟩
  exact
    factorizedAtomPairRealizationOfPair
      D.multiplicative_atoms p hEnergy

/-- Source-path generated stable domains produce atom-pair realizations with
multiplicative factorization readout for both endpoints. -/
theorem factorized_atom_pair_realization_of_source_path_domain
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {n k : Nat}
    (D :
      SourcePathStableTransportAtomProjectionDomain
        Atomic SourceEvidence n)
    (demand :
      RepRepairDemand SourceEvidence D.residual_transport n k) :
    FactorizedAtomPairRealization
      Atomic D.multiplicative_atoms n k := by
  rcases
    atom_pair_realization_of_source_projection_path_nonabsorbed_lift
      D.source_path_nonabsorbed demand with
  ⟨p, hEnergy⟩
  exact
    factorizedAtomPairRealizationOfPair
      D.multiplicative_atoms p hEnergy

/-- Per-shell positive repair lift for atom-pair realizations.

This is the smallest arithmetic socket behind gap persistence: if shell `k`
has an atom-pair realization, transport/repair data produces a realization at
the successor shell.  Negative gap descent should be obtained from this by
contraposition. -/
structure AtomPairSuccessorRepairLift
    (Atomic : Nat -> Prop) (n k : Nat) where
  lift_successor :
    (∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k) ->
    (∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k + 1)

/-- Named forward readout of a per-shell repair lift. -/
theorem atom_pair_successor_realization_of_repair_lift
    {Atomic : Nat -> Prop} {n k : Nat}
    (L : AtomPairSuccessorRepairLift Atomic n k) :
    (∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k) ->
    (∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k + 1) := by
  exact L.lift_successor

/-- A per-shell positive repair lift implies gap persistence by
contraposition. -/
theorem atom_pair_gap_persistence_of_successor_repair_lift
    {Atomic : Nat -> Prop} {n k : Nat}
    (L : AtomPairSuccessorRepairLift Atomic n k) :
    (¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k + 1) ->
    (¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k) := by
  intro hNoSucc hRealized
  exact hNoSucc (L.lift_successor hRealized)

/-- A family of per-shell repair lifts gives the old `gap_descends` shape. -/
theorem gap_descends_of_successor_repair_lift_family
    {Atomic : Nat -> Prop} {n k : Nat}
    (L : ∀ j : Nat, AtomPairSuccessorRepairLift Atomic n j) :
    (¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k + 1) ->
    (¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k) := by
  exact atom_pair_gap_persistence_of_successor_repair_lift (L k)

/-- A structured lift that turns source one-step descent plus arithmetic gap
persistence into atom-projection defect descent.

`gap_descends` is the arithmetic/holonomy obligation: if no atom pair realizes
shell `k + 1`, then no atom pair realizes shell `k`.  This is still a hard
legacy field, but it is isolated from source demand descent.  Prefer building
it from `AtomPairSuccessorRepairLift` when a positive repair mechanism is
available. -/
structure AtomProjectionDefectDescentLift
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  gap_descends :
    ∀ {k : Nat},
      (¬ ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k + 1) ->
      (¬ ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k)

/-- Mechanism-facing defect lift: source demand descends, and arithmetic gaps
descend only because each realized shell repairs to its successor. -/
structure AtomProjectionDefectRepairLift
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  realization_successor :
    ∀ k : Nat, AtomPairSuccessorRepairLift Atomic n k

/-- Convert the mechanism-facing positive repair lift to the older negative
gap-persistence socket. -/
def atomProjectionDefectDescentLiftOfRepairLift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (L :
      AtomProjectionDefectRepairLift
        Atomic SourceEvidence Residual n) :
    AtomProjectionDefectDescentLift
      Atomic SourceEvidence Residual n where
  source_descent := L.source_descent
  gap_descends := by
    intro k hNoSucc
    exact
      atom_pair_gap_persistence_of_successor_repair_lift
        (L.realization_successor k)
        hNoSucc

/-- Positive-direction realization lift.

This is the more mechanism-like arithmetic/repair obligation: a realized
lower shell can be transported or repaired into a realized successor shell.
Gap persistence is then obtained by contraposition, instead of being assumed as
a primitive negative fact. -/
structure AtomPairRealizationTransportLift
    (Atomic : Nat -> Prop) (n : Nat) where
  lift_realization :
    ∀ {k : Nat},
      (∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k) ->
      (∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k + 1)

/-- A global realization transport supplies every per-shell repair lift. -/
theorem atomPairSuccessorRepairLiftOfRealizationTransportLift
    {Atomic : Nat -> Prop} {n : Nat}
    (L : AtomPairRealizationTransportLift Atomic n)
    (k : Nat) :
    AtomPairSuccessorRepairLift Atomic n k := by
  exact { lift_successor := L.lift_realization }

/-- Per-shell repair lifts can be repackaged as the older global transport
interface. -/
theorem atomPairRealizationTransportLiftOfSuccessorRepairFamily
    {Atomic : Nat -> Prop} {n : Nat}
    (L : ∀ k : Nat, AtomPairSuccessorRepairLift Atomic n k) :
    AtomPairRealizationTransportLift Atomic n := by
  exact {
    lift_realization := by
      intro k hRealized
      exact (L k).lift_successor hRealized
  }

/-- A global realization transport supplies the mechanism-facing defect lift. -/
def atomProjectionDefectRepairLiftOfRealizationTransport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (realization_lift :
      AtomPairRealizationTransportLift Atomic n) :
    AtomProjectionDefectRepairLift
      Atomic SourceEvidence Residual n where
  source_descent := source
  realization_successor :=
    atomPairSuccessorRepairLiftOfRealizationTransportLift realization_lift

/-- Named forward readout of a positive-direction realization lift.

This is intentionally separate from the negative `gap_descends` use site:
first construct a successor-shell realization, then take the contrapositive
only where a defect proof needs it. -/
theorem atom_pair_realization_successor_of_transport_lift
    {Atomic : Nat -> Prop} {n k : Nat}
    (L : AtomPairRealizationTransportLift Atomic n) :
    (∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k) ->
    (∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k + 1) := by
  exact L.lift_realization

/-- Positive lift implies gap persistence by contraposition.

This isolates the logical move used by `gap_descends`: the mathematical
obligation is the forward transport/repair lift, not a primitive downward
propagation of non-realization. -/
theorem atom_pair_gap_persistence_of_successor_realization
    {Atomic : Nat -> Prop} {n k : Nat}
    (successor :
      (∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k) ->
      (∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k + 1)) :
    (¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k + 1) ->
    (¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k) := by
  intro hNoSucc hRealized
  exact hNoSucc (successor hRealized)

/-- A transport/repair realization lift gives shell-gap persistence, with the
forward lift exposed as the first step. -/
theorem atom_pair_gap_persistence_of_realization_transport_lift
    {Atomic : Nat -> Prop} {n k : Nat}
    (L : AtomPairRealizationTransportLift Atomic n) :
    (¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k + 1) ->
    (¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k) := by
  exact
    atom_pair_gap_persistence_of_successor_realization
      (atom_pair_realization_successor_of_transport_lift L)

/-- Pair-level energy successor transport.

This is lower-level than `AtomPairRealizationTransportLift`: it transports an
actual arithmetic atom-pair object to a successor-shell atom-pair object.  The
returned object is still an `ArithmeticAtomPair Atomic n`, so atomhood is
preserved by construction rather than by an endpoint table. -/
structure AtomPairEnergySuccessorTransport
    (Atomic : Nat -> Prop) (n : Nat) where
  liftPair :
    ArithmeticAtomPair Atomic n ->
      ArithmeticAtomPair Atomic n
  energy_lift :
    ∀ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy (liftPair p) =
        ArithmeticAtomPair.energy p + 1

/-- Certificate that the realized atom-pair spectrum has a maximum energy.

This is a boundary object: when such a maximum exists, a global pair-level
successor transport cannot exist.  Therefore `AtomPairEnergySuccessorTransport`
cannot be justified by a finite endpoint table with a top shell. -/
structure AtomPairMaxEnergyCertificate
    (Atomic : Nat -> Prop) (n : Nat) where
  maxPair : ArithmeticAtomPair Atomic n
  maxEnergy :
    ∀ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p ≤
        ArithmeticAtomPair.energy maxPair

/-- A global pair-level energy successor transport is impossible when the
realized atom-pair spectrum has a maximum energy. -/
theorem no_pair_energy_successor_transport_of_max_energy
    {Atomic : Nat -> Prop} {n : Nat}
    (M : AtomPairMaxEnergyCertificate Atomic n) :
    AtomPairEnergySuccessorTransport Atomic n -> False := by
  intro T
  have hle :
      ArithmeticAtomPair.energy (T.liftPair M.maxPair) ≤
        ArithmeticAtomPair.energy M.maxPair :=
    M.maxEnergy (T.liftPair M.maxPair)
  rw [T.energy_lift M.maxPair] at hle
  exact Nat.not_succ_le_self
    (ArithmeticAtomPair.energy M.maxPair)
    (by
      simpa [Nat.succ_eq_add_one] using hle)

/-- Local pair-level energy successor transport up to a target shell.

Unlike `AtomPairEnergySuccessorTransport`, this bounded version only transports
pairs whose energy is below `bound`.  It is the right interface for excluding a
specific target-shell defect without pretending that a finite or topped-out
spectrum has a global successor operator. -/
structure BoundedAtomPairEnergySuccessorTransport
    (Atomic : Nat -> Prop) (n bound : Nat) where
  liftPair :
    (p : ArithmeticAtomPair Atomic n) ->
      ArithmeticAtomPair.energy p < bound ->
        ArithmeticAtomPair Atomic n
  energy_lift :
    ∀ (p : ArithmeticAtomPair Atomic n)
      (hEnergy : ArithmeticAtomPair.energy p < bound),
        ArithmeticAtomPair.energy (liftPair p hEnergy) =
          ArithmeticAtomPair.energy p + 1

/-- A bounded transport can be restricted to a smaller bound. -/
def boundedPairEnergySuccessorTransportRestrict
    {Atomic : Nat -> Prop} {n lower upper : Nat}
    (T : BoundedAtomPairEnergySuccessorTransport Atomic n upper)
    (hBound : lower ≤ upper) :
    BoundedAtomPairEnergySuccessorTransport Atomic n lower where
  liftPair := fun p hEnergy =>
    T.liftPair p (Nat.lt_of_lt_of_le hEnergy hBound)
  energy_lift := fun p hEnergy =>
    T.energy_lift p (Nat.lt_of_lt_of_le hEnergy hBound)

/-- Bounded pair transport gives a realization lift below the bound. -/
theorem bounded_realization_transport_lift_of_pair_transport
    {Atomic : Nat -> Prop} {n bound k : Nat}
    (T : BoundedAtomPairEnergySuccessorTransport Atomic n bound)
    (hk : k < bound) :
    (∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k) ->
    (∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k + 1) := by
  intro hRealized
  rcases hRealized with ⟨p, hEnergy⟩
  have hpBelow : ArithmeticAtomPair.energy p < bound := by
    rw [hEnergy]
    exact hk
  refine ⟨T.liftPair p hpBelow, ?_⟩
  calc
    ArithmeticAtomPair.energy (T.liftPair p hpBelow) =
        ArithmeticAtomPair.energy p + 1 := T.energy_lift p hpBelow
    _ = k + 1 := by
      rw [hEnergy]

/-- Bounded pair transport gives gap persistence below the bound by
contraposition. -/
theorem bounded_gap_descends_of_pair_transport
    {Atomic : Nat -> Prop} {n bound k : Nat}
    (T : BoundedAtomPairEnergySuccessorTransport Atomic n bound)
    (hk : k < bound) :
    (¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k + 1) ->
    (¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k) := by
  intro hNoSucc hRealized
  exact hNoSucc
    (bounded_realization_transport_lift_of_pair_transport T hk hRealized)

/-- A pair-level successor transport induces the existential realization lift. -/
theorem atomPairRealizationTransportLiftOfPairTransport
    {Atomic : Nat -> Prop} {n : Nat}
    (T : AtomPairEnergySuccessorTransport Atomic n) :
    AtomPairRealizationTransportLift Atomic n := by
  refine { lift_realization := ?_ }
  intro k hRealized
  rcases hRealized with ⟨p, hEnergy⟩
  refine ⟨T.liftPair p, ?_⟩
  calc
    ArithmeticAtomPair.energy (T.liftPair p) =
        ArithmeticAtomPair.energy p + 1 := T.energy_lift p
    _ = k + 1 := by
      rw [hEnergy]

/-- Even the existential realization transport lift is impossible when the
realized atom-pair spectrum has a maximum energy. -/
theorem no_realization_transport_lift_of_max_energy
    {Atomic : Nat -> Prop} {n : Nat}
    (M : AtomPairMaxEnergyCertificate Atomic n) :
    ¬ AtomPairRealizationTransportLift Atomic n := by
  intro L
  have hRealized :
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p =
          ArithmeticAtomPair.energy M.maxPair :=
    ⟨M.maxPair, rfl⟩
  rcases L.lift_realization hRealized with ⟨p, hpEnergy⟩
  have hle :
      ArithmeticAtomPair.energy p ≤
        ArithmeticAtomPair.energy M.maxPair :=
    M.maxEnergy p
  rw [hpEnergy] at hle
  exact Nat.not_succ_le_self
    (ArithmeticAtomPair.energy M.maxPair)
    (by
      simpa [Nat.succ_eq_add_one] using hle)

/-- Contrapositive readout: a positive-direction realization lift implies
gap persistence from shell `k + 1` down to shell `k`. -/
theorem gap_descends_of_realization_transport_lift
    {Atomic : Nat -> Prop} {n k : Nat}
    (L : AtomPairRealizationTransportLift Atomic n) :
    (¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k + 1) ->
    (¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k) := by
  exact atom_pair_gap_persistence_of_realization_transport_lift L

/-!
## Traced feasible defect finite descent

The untraced finite-descent socket lowers `AtomProjectionDefect`.  This traced
version keeps feasibility and source-production trace data inside the defect
object while it descends to the terminal no-third-sink contradiction.
-/

/-- Terminal no-third-sink law specialized to traced feasible projection
defects. -/
structure TracedFeasibleAtomProjectionTerminalNoThirdSink
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  absorbed_static : Prop
  projected_repair : Prop
  no_third_sink :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) ->
      headroom_nonzero ->
        absorbed_static ∨ projected_repair
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  defect_forbids_projected_repair :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) ->
      ¬ projected_repair

/-- Terminal projected-repair readout for traced feasible demands.

The branch identifies a terminal traced feasible source demand and asserts
that the faithful partial projection is defined there.  The atom pair is read
from the projection functor, not supplied as a separate witness. -/
structure TracedTerminalProjectionDefinedReadout
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  projected_repair : Prop
  terminal_demand :
    projected_repair ->
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n 0
  projection_defined :
    ∀ hProjected : projected_repair,
      Projection.project
          (terminal_demand hProjected).demand.demand.evidence ≠ none

/-- Terminal projected-repair readout where projection failure is absorbed.

Nonzero headroom can later rule out absorption, forcing defined projection
on the same traced terminal demand. -/
structure TracedTerminalProjectionNonabsorbedReadout
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual)
    (absorbed_static : Prop) where
  projected_repair : Prop
  terminal_demand :
    projected_repair ->
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n 0
  projection_undefined_absorbs :
    ∀ hProjected : projected_repair,
      Projection.project
          (terminal_demand hProjected).demand.demand.evidence = none ->
        absorbed_static

/-- A traced nonabsorbed readout gives defined projection once absorption has
been ruled out. -/
theorem traced_projection_defined_of_nonabsorbed_readout
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    {absorbed_static : Prop}
    (R :
      TracedTerminalProjectionNonabsorbedReadout
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection absorbed_static)
    (hNotAbsorbed : ¬ absorbed_static) :
    ∀ hProjected : R.projected_repair,
      Projection.project
          (R.terminal_demand hProjected).demand.demand.evidence ≠ none := by
  intro hProjected hNone
  exact hNotAbsorbed
    (R.projection_undefined_absorbs hProjected hNone)

/-- A traced nonabsorbed readout induces a traced defined-projection readout
once absorption has been ruled out. -/
def tracedTerminalProjectionDefinedReadoutOfNonabsorbed
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    {absorbed_static : Prop}
    (R :
      TracedTerminalProjectionNonabsorbedReadout
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection absorbed_static)
    (hNotAbsorbed : ¬ absorbed_static) :
    TracedTerminalProjectionDefinedReadout
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n Projection where
  projected_repair := R.projected_repair
  terminal_demand := R.terminal_demand
  projection_defined :=
    traced_projection_defined_of_nonabsorbed_readout R hNotAbsorbed

/-- A traced defined projection readout materializes the terminal atom-pair
realization by projection faithfulness. -/
theorem projected_repair_realizes_of_traced_terminal_defined_readout
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (R :
      TracedTerminalProjectionDefinedReadout
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection) :
    R.projected_repair ->
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = 0 := by
  intro hProjected
  exact
    atom_pair_realization_of_defined_projected_demand
      Projection
      (R.terminal_demand hProjected).demand.demand
      (R.projection_defined hProjected)

/-- Traced terminal no-third-sink law with a materialized projected-repair
branch. -/
structure TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  absorbed_static : Prop
  projected_repair : Prop
  no_third_sink :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) ->
      headroom_nonzero ->
        absorbed_static ∨ projected_repair
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static
  projected_repair_realizes :
    projected_repair ->
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = 0

/-- Traced terminal no-third-sink where the projected branch is read from a
defined faithful projection on a terminal traced demand. -/
structure TracedFeasibleAtomProjectionTerminalDefinedNoThirdSink
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  absorbed_static : Prop
  projected_readout :
    TracedTerminalProjectionDefinedReadout
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n Projection
  no_third_sink :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) ->
      headroom_nonzero ->
        absorbed_static ∨ projected_readout.projected_repair
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static

/-- Traced terminal no-third-sink where projection failure in the projected
branch would force absorbed-static. -/
structure TracedFeasibleAtomProjectionTerminalNonabsorbedNoThirdSink
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat)
    (Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual) where
  headroom_nonzero : Prop
  headroom_witness : headroom_nonzero
  absorbed_static : Prop
  projected_readout :
    TracedTerminalProjectionNonabsorbedReadout
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n Projection absorbed_static
  no_third_sink :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) ->
      headroom_nonzero ->
        absorbed_static ∨ projected_readout.projected_repair
  nonzero_forbids_absorbed_static :
    headroom_nonzero -> ¬ absorbed_static

/-- A traced defined no-third-sink law induces a materializing terminal law by
faithful projection readout. -/
def tracedFeasibleAtomProjectionTerminalMaterializingNoThirdSinkOfDefined
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      TracedFeasibleAtomProjectionTerminalDefinedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection) :
    TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n where
  headroom_nonzero := L.headroom_nonzero
  headroom_witness := L.headroom_witness
  absorbed_static := L.absorbed_static
  projected_repair := L.projected_readout.projected_repair
  no_third_sink := L.no_third_sink
  nonzero_forbids_absorbed_static :=
    L.nonzero_forbids_absorbed_static
  projected_repair_realizes :=
    projected_repair_realizes_of_traced_terminal_defined_readout
      L.projected_readout

/-- A traced nonabsorbed terminal law induces the defined terminal law by
using nonzero headroom to rule out absorbed-static projection failure. -/
def tracedFeasibleAtomProjectionTerminalDefinedNoThirdSinkOfNonabsorbed
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      TracedFeasibleAtomProjectionTerminalNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection) :
    TracedFeasibleAtomProjectionTerminalDefinedNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n Projection where
  headroom_nonzero := L.headroom_nonzero
  headroom_witness := L.headroom_witness
  absorbed_static := L.absorbed_static
  projected_readout :=
    tracedTerminalProjectionDefinedReadoutOfNonabsorbed
      L.projected_readout
      (L.nonzero_forbids_absorbed_static L.headroom_witness)
  no_third_sink := L.no_third_sink
  nonzero_forbids_absorbed_static :=
    L.nonzero_forbids_absorbed_static

/-- A traced nonabsorbed terminal law induces the materializing terminal law. -/
def tracedFeasibleAtomProjectionTerminalMaterializingNoThirdSinkOfNonabsorbed
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      TracedFeasibleAtomProjectionTerminalNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection) :
    TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n :=
  tracedFeasibleAtomProjectionTerminalMaterializingNoThirdSinkOfDefined
    (tracedFeasibleAtomProjectionTerminalDefinedNoThirdSinkOfNonabsorbed L)

/-- A traced materializing terminal law induces the older traced terminal law
by reading `not projected_repair` from the defect's missing-realization side. -/
def tracedFeasibleAtomProjectionTerminalNoThirdSinkOfMaterializing
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (L :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    TracedFeasibleAtomProjectionTerminalNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n where
  headroom_nonzero := L.headroom_nonzero
  headroom_witness := L.headroom_witness
  absorbed_static := L.absorbed_static
  projected_repair := L.projected_repair
  no_third_sink := L.no_third_sink
  nonzero_forbids_absorbed_static :=
    L.nonzero_forbids_absorbed_static
  defect_forbids_projected_repair := by
    intro hDefect hProjected
    rcases hDefect with ⟨defect⟩
    exact defect.noAtomRealization
      (L.projected_repair_realizes hProjected)

/-- Terminal traced feasible projection defects are impossible under the
two-branch no-third-sink disposition. -/
theorem no_terminal_traced_feasible_atom_projection_defect_of_no_third_sink
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (L :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) := by
  intro hTerminal
  cases L.no_third_sink hTerminal L.headroom_witness with
  | inl hAbsorbed =>
      exact L.nonzero_forbids_absorbed_static
        L.headroom_witness hAbsorbed
  | inr hProjected =>
      exact L.defect_forbids_projected_repair hTerminal hProjected

/-- Terminal traced feasible defects are impossible when no-third-sink's
projected branch materializes an atom-pair realization. -/
theorem no_terminal_traced_feasible_atom_projection_defect_of_materializing_no_third_sink
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (L :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) :=
  no_terminal_traced_feasible_atom_projection_defect_of_no_third_sink
    (tracedFeasibleAtomProjectionTerminalNoThirdSinkOfMaterializing L)

/-- Once an actual terminal traced demand is already present, merely
inhabiting the abstract materializing no-third-sink socket is equivalent to
already having the requested energy-zero atom-pair realization.

The forward implication turns a hypothetical missing realization into the
terminal defect excluded by the law.  The reverse implication records that an
existing realization can fill the abstract projected branch directly.  Thus
this is a strength/vacuity boundary: in a concrete producer chain, constructing
the materializing law cannot be counted as a lightweight adapter after the
terminal demand has been generated. -/
theorem
    nonempty_traced_feasible_terminal_materializing_no_third_sink_iff_atom_pair_realization_of_demand
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n 0) :
    Nonempty
        (TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n) ↔
      ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = 0 := by
  constructor
  · rintro ⟨law⟩
    by_contra noRealization
    exact
      (no_terminal_traced_feasible_atom_projection_defect_of_materializing_no_third_sink
        law)
        ⟨{ demand := demand
           noAtomRealization := noRealization }⟩
  · rintro ⟨pair, energyZero⟩
    exact
      ⟨{ headroom_nonzero := True
         headroom_witness := True.intro
         absorbed_static := False
         projected_repair := True
         no_third_sink := by
           intro _defect _headroom
           exact Or.inr True.intro
         nonzero_forbids_absorbed_static := by
           intro _headroom absorbed
           exact absorbed.elim
         projected_repair_realizes := by
           intro _projected
           exact ⟨pair, energyZero⟩ }⟩

/-- Terminal traced feasible defects are impossible when the projected branch
has defined faithful projection readout. -/
theorem no_terminal_traced_feasible_atom_projection_defect_of_defined_no_third_sink
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      TracedFeasibleAtomProjectionTerminalDefinedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) :=
  no_terminal_traced_feasible_atom_projection_defect_of_materializing_no_third_sink
    (tracedFeasibleAtomProjectionTerminalMaterializingNoThirdSinkOfDefined L)

/-- Terminal traced feasible defects are impossible when projection failure in
the projected branch would force absorbed-static. -/
theorem no_terminal_traced_feasible_atom_projection_defect_of_nonabsorbed_no_third_sink
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (L :
      TracedFeasibleAtomProjectionTerminalNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) :=
  no_terminal_traced_feasible_atom_projection_defect_of_defined_no_third_sink
    (tracedFeasibleAtomProjectionTerminalDefinedNoThirdSinkOfNonabsorbed L)

/-- Traced feasible defect descent lift.

The source side lowers the feasible demand while preserving trace; the
arithmetic side lowers projection gaps by the positive-transport/contrapositive
route recorded in `gap_descends`. -/
structure TracedFeasibleAtomProjectionDefectDescentLift
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  trace_descent :
    SourceRepairTraceDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n
  gap_descends :
    ∀ {k : Nat},
      (¬ ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k + 1) ->
      (¬ ∃ p : ArithmeticAtomPair Atomic n,
        ArithmeticAtomPair.energy p = k)

/-- Mechanism-facing traced feasible defect lift.

The source and trace data descend on the representation side; arithmetic gap
descent is not primitive, but is generated from per-shell positive repair
lifts for atom-pair realizations. -/
structure TracedFeasibleAtomProjectionDefectRepairLift
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  trace_descent :
    SourceRepairTraceDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n
  realization_successor :
    ∀ k : Nat, AtomPairSuccessorRepairLift Atomic n k

/-- Convert the traced positive repair lift to the older negative
gap-persistence socket. -/
def tracedFeasibleAtomProjectionDefectDescentLiftOfRepairLift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (L :
      TracedFeasibleAtomProjectionDefectRepairLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    TracedFeasibleAtomProjectionDefectDescentLift
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n where
  source_descent := L.source_descent
  step_path := L.step_path
  trace_descent := L.trace_descent
  gap_descends := by
    intro k hNoSucc
    exact
      atom_pair_gap_persistence_of_successor_repair_lift
        (L.realization_successor k)
        hNoSucc

/-- A global realization transport supplies the traced positive repair lift. -/
def tracedFeasibleAtomProjectionDefectRepairLiftOfRealizationTransport
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (realization_lift :
      AtomPairRealizationTransportLift Atomic n) :
    TracedFeasibleAtomProjectionDefectRepairLift
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n where
  source_descent := source
  step_path := step_path
  trace_descent := trace_descent
  realization_successor :=
    atomPairSuccessorRepairLiftOfRealizationTransportLift realization_lift

/-- Build the traced feasible defect-descent lift from source/trace descent
plus positive realization transport. -/
def tracedFeasibleAtomProjectionDefectDescentLiftOfRealizationTransport
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (realization_lift :
      AtomPairRealizationTransportLift Atomic n) :
    TracedFeasibleAtomProjectionDefectDescentLift
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n :=
  tracedFeasibleAtomProjectionDefectDescentLiftOfRepairLift
    (tracedFeasibleAtomProjectionDefectRepairLiftOfRealizationTransport
      source step_path trace_descent realization_lift)

/-- Traced feasible defect descent derived from source/trace descent plus
arithmetic gap persistence. -/
theorem traced_feasible_atom_projection_defect_descend_of_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (L :
      TracedFeasibleAtomProjectionDefectDescentLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n (k + 1)) ->
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) := by
  intro hDefect
  rcases hDefect with ⟨defect⟩
  exact ⟨{
    demand :=
      lowerTracedFeasibleDemandOfSourceStep
        L.source_descent L.step_path L.trace_descent defect.demand
    noAtomRealization :=
      L.gap_descends defect.noAtomRealization
  }⟩

/-- Traced feasible defect descent using the mechanism-facing positive repair
lift.  This is the traced version of the intended split:

```text
realization at k
-> repair lift
-> realization at k+1
-> contrapositive gap persistence
``` -/
theorem traced_feasible_atom_projection_defect_descend_of_repair_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (L :
      TracedFeasibleAtomProjectionDefectRepairLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n (k + 1)) ->
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) :=
  traced_feasible_atom_projection_defect_descend_of_lift
    (tracedFeasibleAtomProjectionDefectDescentLiftOfRepairLift L)

/-- Finite-descent domain for traced feasible atom-projection defects. -/
structure TracedFeasibleAtomProjectionDefectDescentDomain
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  terminal_no_third_sink :
    TracedFeasibleAtomProjectionTerminalNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n
  descend :
    ∀ {k : Nat},
      Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n (k + 1)) ->
      Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k)

/-- Build the traced feasible descent domain from terminal no-third-sink and
the separated descent lift. -/
def tracedFeasibleAtomProjectionDefectDescentDomainOfLift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (lift :
      TracedFeasibleAtomProjectionDefectDescentLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    TracedFeasibleAtomProjectionDefectDescentDomain
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n where
  terminal_no_third_sink := terminal
  descend := traced_feasible_atom_projection_defect_descend_of_lift lift

/-- Finite descent plus terminal no-third-sink excludes all traced feasible
atom-projection defects for a fixed fiber `n`. -/
theorem no_traced_feasible_atom_projection_defect_by_finite_descent
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (D :
      TracedFeasibleAtomProjectionDefectDescentDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k) := by
  intro k
  induction k with
  | zero =>
      exact
        no_terminal_traced_feasible_atom_projection_defect_of_no_third_sink
          D.terminal_no_third_sink
  | succ k ih =>
      intro hDefect
      exact ih (D.descend hDefect)

/-- Demand-level traced finite-descent theorem.

The output remains `¬¬ exists atom pair`; no endpoint witness is extracted
from a finite table. -/
theorem not_not_atom_realization_of_traced_feasible_demand_by_finite_descent
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (D :
      TracedFeasibleAtomProjectionDefectDescentDomain
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k := by
  intro hMissing
  exact (no_traced_feasible_atom_projection_defect_by_finite_descent D k)
    ⟨{ demand := demand, noAtomRealization := hMissing }⟩

/-- Convenience theorem: traced source/trace descent plus arithmetic gap
persistence and terminal no-third-sink exclude all traced feasible defects. -/
theorem no_traced_feasible_atom_projection_defect_by_lift_and_no_third_sink
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (lift :
      TracedFeasibleAtomProjectionDefectDescentLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_atom_projection_defect_by_finite_descent
    (tracedFeasibleAtomProjectionDefectDescentDomainOfLift terminal lift)

/-- Traced convenience theorem using source/trace descent plus per-shell
positive repair lifts; gap persistence is obtained only by contraposition. -/
theorem no_traced_feasible_atom_projection_defect_by_repair_lift_and_no_third_sink
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (lift :
      TracedFeasibleAtomProjectionDefectRepairLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_atom_projection_defect_by_lift_and_no_third_sink
    terminal
    (tracedFeasibleAtomProjectionDefectDescentLiftOfRepairLift lift)

/-- Demand-level version of the separated traced lift theorem. -/
theorem not_not_atom_realization_of_traced_feasible_demand_by_lift_and_no_third_sink
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (lift :
      TracedFeasibleAtomProjectionDefectDescentLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_traced_feasible_demand_by_finite_descent
    (tracedFeasibleAtomProjectionDefectDescentDomainOfLift terminal lift)
    demand

/-- Demand-level traced theorem using per-shell positive repair lifts. -/
theorem not_not_atom_realization_of_traced_feasible_demand_by_repair_lift_and_no_third_sink
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (lift :
      TracedFeasibleAtomProjectionDefectRepairLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_traced_feasible_demand_by_lift_and_no_third_sink
    terminal
    (tracedFeasibleAtomProjectionDefectDescentLiftOfRepairLift lift)
    demand

/-- Traced finite-descent theorem with a materializing terminal no-third-sink
law.  The projected-repair branch is converted into the older terminal law by
reading the terminal atom-pair realization, not by assuming a primitive
`not projected_repair` field. -/
theorem no_traced_feasible_atom_projection_defect_by_materializing_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (lift :
      TracedFeasibleAtomProjectionDefectDescentLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_atom_projection_defect_by_lift_and_no_third_sink
    (tracedFeasibleAtomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    lift

/-- Demand-level traced finite-descent theorem with a materializing terminal
law. -/
theorem not_not_atom_realization_of_traced_feasible_demand_by_materializing_lift
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (lift :
      TracedFeasibleAtomProjectionDefectDescentLift
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_traced_feasible_demand_by_lift_and_no_third_sink
    (tracedFeasibleAtomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    lift
    demand

/-- Convenience theorem using positive-direction realization transport instead
of a primitive negative gap-persistence field. -/
theorem no_traced_feasible_atom_projection_defect_by_realization_transport
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (realization_lift :
      AtomPairRealizationTransportLift Atomic n) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_atom_projection_defect_by_lift_and_no_third_sink
    terminal
    (tracedFeasibleAtomProjectionDefectDescentLiftOfRealizationTransport
      source step_path trace_descent realization_lift)

/-- Demand-level traced theorem using positive-direction realization
transport. -/
theorem not_not_atom_realization_of_traced_feasible_demand_by_realization_transport
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (terminal :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (realization_lift :
      AtomPairRealizationTransportLift Atomic n)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_traced_feasible_demand_by_lift_and_no_third_sink
    terminal
    (tracedFeasibleAtomProjectionDefectDescentLiftOfRealizationTransport
      source step_path trace_descent realization_lift)
    demand

/-- Materializing-terminal version using positive-direction realization
transport. -/
theorem no_traced_feasible_atom_projection_defect_by_materializing_realization_transport
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n : Nat}
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (realization_lift :
      AtomPairRealizationTransportLift Atomic n) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_atom_projection_defect_by_realization_transport
    (tracedFeasibleAtomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    source step_path trace_descent realization_lift

/-- Demand-level materializing-terminal version using positive-direction
realization transport. -/
theorem not_not_atom_realization_of_traced_feasible_demand_by_materializing_realization_transport
    {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {Source : RepresentationFeasibleCategory SourceEvidence}
    {n k : Nat}
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (step_path :
      ResidualStepSourcePathCompatibility SourceEvidence Residual Source)
    (trace_descent :
      SourceRepairTraceDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n)
    (realization_lift :
      AtomPairRealizationTransportLift Atomic n)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_traced_feasible_demand_by_realization_transport
    (tracedFeasibleAtomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    source step_path trace_descent realization_lift
    demand

/-- Build the defect-descent lift from source demand descent plus positive
realization transport. -/
def atomProjectionDefectDescentLiftOfRealizationTransport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (realization_lift :
      AtomPairRealizationTransportLift Atomic n) :
    AtomProjectionDefectDescentLift
      Atomic SourceEvidence Residual n :=
  atomProjectionDefectDescentLiftOfRepairLift
    (atomProjectionDefectRepairLiftOfRealizationTransport
      source realization_lift)

/-- Defect descent derived from source demand descent plus arithmetic gap
persistence. -/
theorem atom_projection_defect_descend_of_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (L :
      AtomProjectionDefectDescentLift
        Atomic SourceEvidence Residual n) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) := by
  intro hDefect
  rcases hDefect with ⟨defect⟩
  exact ⟨{
    demand := lowerDemandOfSourceStep L.source_descent defect.demand
    noAtomRealization := L.gap_descends defect.noAtomRealization
  }⟩

/-- Defect descent using the mechanism-facing positive repair lift.

This theorem performs the requested split explicitly: source demand is lowered,
and the missing successor realization is pulled back only as the
contrapositive of `realization at k -> repaired realization at k+1`. -/
theorem atom_projection_defect_descend_of_repair_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (L :
      AtomProjectionDefectRepairLift
        Atomic SourceEvidence Residual n) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  atom_projection_defect_descend_of_lift
    (atomProjectionDefectDescentLiftOfRepairLift L)

/-- Build the previous descent domain from its separated source and arithmetic
obligations. -/
def atomProjectionDefectDescentDomainOfLift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (lift :
      AtomProjectionDefectDescentLift
        Atomic SourceEvidence Residual n) :
    AtomProjectionDefectDescentDomain
      Atomic SourceEvidence Residual n where
  terminal_no_third_sink := terminal
  descend := atom_projection_defect_descend_of_lift lift

/-- Finite descent plus terminal no-third-sink excludes all stable
atom-projection defects for a fixed fiber `n`. -/
theorem no_atom_projection_defect_by_finite_descent
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (D :
      AtomProjectionDefectDescentDomain
        Atomic SourceEvidence Residual n) :
    ∀ k : Nat,
      ¬ Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n k) := by
  intro k
  induction k with
  | zero =>
      exact no_terminal_atom_projection_defect_of_no_third_sink
        D.terminal_no_third_sink
  | succ k ih =>
      intro hDefect
      exact ih (D.descend hDefect)

/-- For a concrete source demand, finite descent/no-third-sink rules out the
missing-realization branch.

The result is deliberately `¬¬ exists atom pair`, not a returned witness. -/
theorem not_not_atom_realization_of_demand_by_finite_descent
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (D :
      AtomProjectionDefectDescentDomain
        Atomic SourceEvidence Residual n)
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k := by
  intro hMissing
  exact (no_atom_projection_defect_by_finite_descent D k)
    ⟨{ demand := demand, noAtomRealization := hMissing }⟩

/-- Convenience theorem: separated source descent plus arithmetic gap
persistence and terminal no-third-sink exclude all atom-projection defects. -/
theorem no_atom_projection_defect_by_lift_and_no_third_sink
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (lift :
      AtomProjectionDefectDescentLift
        Atomic SourceEvidence Residual n) :
    ∀ k : Nat,
      ¬ Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  no_atom_projection_defect_by_finite_descent
    (atomProjectionDefectDescentDomainOfLift terminal lift)

/-- Convenience theorem using source descent plus per-shell positive repair
lifts, with gap persistence obtained by contraposition. -/
theorem no_atom_projection_defect_by_repair_lift_and_no_third_sink
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (lift :
      AtomProjectionDefectRepairLift
        Atomic SourceEvidence Residual n) :
    ∀ k : Nat,
      ¬ Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  no_atom_projection_defect_by_lift_and_no_third_sink
    terminal
    (atomProjectionDefectDescentLiftOfRepairLift lift)

/-- For a concrete source demand, the separated lift version rules out the
missing-realization branch without returning an atom-pair witness. -/
theorem not_not_atom_realization_of_demand_by_lift_and_no_third_sink
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (lift :
      AtomProjectionDefectDescentLift
        Atomic SourceEvidence Residual n)
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_demand_by_finite_descent
    (atomProjectionDefectDescentDomainOfLift terminal lift)
    demand

/-- Demand-level theorem using per-shell positive repair lifts. -/
theorem not_not_atom_realization_of_demand_by_repair_lift_and_no_third_sink
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (lift :
      AtomProjectionDefectRepairLift
        Atomic SourceEvidence Residual n)
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_demand_by_lift_and_no_third_sink
    terminal
    (atomProjectionDefectDescentLiftOfRepairLift lift)
    demand

/-- Finite descent with a materializing terminal no-third-sink law excludes all
stable atom-projection defects.  The terminal projected-repair branch is
converted into an atom-pair realization, not assumed as a naked
`¬ projected_repair` field. -/
theorem no_atom_projection_defect_by_materializing_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (lift :
      AtomProjectionDefectDescentLift
        Atomic SourceEvidence Residual n) :
    ∀ k : Nat,
      ¬ Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  no_atom_projection_defect_by_lift_and_no_third_sink
    (atomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    lift

/-- Demand-level materializing finite-descent theorem. -/
theorem not_not_atom_realization_of_demand_by_materializing_lift
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (lift :
      AtomProjectionDefectDescentLift
        Atomic SourceEvidence Residual n)
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_demand_by_lift_and_no_third_sink
    (atomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    lift
    demand

/-- Convenience theorem using the positive-direction realization transport
lift instead of a primitive negative gap-persistence field. -/
theorem no_atom_projection_defect_by_realization_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (realization_lift :
      AtomPairRealizationTransportLift Atomic n) :
    ∀ k : Nat,
      ¬ Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  no_atom_projection_defect_by_lift_and_no_third_sink
    terminal
    (atomProjectionDefectDescentLiftOfRealizationTransport
      source realization_lift)

/-- Demand-level version using positive-direction realization transport. -/
theorem not_not_atom_realization_of_demand_by_realization_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (realization_lift :
      AtomPairRealizationTransportLift Atomic n)
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_demand_by_lift_and_no_third_sink
    terminal
    (atomProjectionDefectDescentLiftOfRealizationTransport
      source realization_lift)
    demand

/-- Materializing-terminal version using positive-direction realization
transport. -/
theorem no_atom_projection_defect_by_materializing_realization_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (realization_lift :
      AtomPairRealizationTransportLift Atomic n) :
    ∀ k : Nat,
      ¬ Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  no_atom_projection_defect_by_realization_transport
    (atomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    source
    realization_lift

/-- Demand-level materializing-terminal version using positive-direction
realization transport. -/
theorem not_not_atom_realization_of_demand_by_materializing_realization_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (realization_lift :
      AtomPairRealizationTransportLift Atomic n)
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_demand_by_realization_transport
    (atomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    source
    realization_lift
    demand

/-- Convenience theorem using a pair-level energy successor transport. -/
theorem no_atom_projection_defect_by_pair_energy_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (pair_transport :
      AtomPairEnergySuccessorTransport Atomic n) :
    ∀ k : Nat,
      ¬ Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  no_atom_projection_defect_by_realization_transport
    terminal source
    (atomPairRealizationTransportLiftOfPairTransport pair_transport)

/-- Demand-level version using a pair-level energy successor transport. -/
theorem not_not_atom_realization_of_demand_by_pair_energy_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (pair_transport :
      AtomPairEnergySuccessorTransport Atomic n)
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_demand_by_realization_transport
    terminal source
    (atomPairRealizationTransportLiftOfPairTransport pair_transport)
    demand

/-- Materializing-terminal version using a pair-level energy successor
transport. -/
theorem no_atom_projection_defect_by_materializing_pair_energy_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (pair_transport :
      AtomPairEnergySuccessorTransport Atomic n) :
    ∀ k : Nat,
      ¬ Nonempty (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  no_atom_projection_defect_by_pair_energy_transport
    (atomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    source
    pair_transport

/-- Demand-level materializing-terminal version using a pair-level energy
successor transport. -/
theorem not_not_atom_realization_of_demand_by_materializing_pair_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n k : Nat}
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (pair_transport :
      AtomPairEnergySuccessorTransport Atomic n)
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_demand_by_pair_energy_transport
    (atomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    source
    pair_transport
    demand

/-- One-step defect descent using bounded pair transport below the target
bound. -/
theorem atom_projection_defect_descend_of_bounded_pair_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound k : Nat}
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (pair_transport :
      BoundedAtomPairEnergySuccessorTransport Atomic n bound)
    (hk : k < bound) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) := by
  intro hDefect
  rcases hDefect with ⟨defect⟩
  exact ⟨{
    demand := lowerDemandOfSourceStep source defect.demand
    noAtomRealization :=
      bounded_gap_descends_of_pair_transport
        pair_transport hk defect.noAtomRealization
  }⟩

/-- To exclude a specific target shell `bound`, it is enough to have pair-level
successor transport strictly below that bound. -/
theorem no_atom_projection_defect_at_bound_by_bounded_pair_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n) :
    ∀ bound : Nat,
      BoundedAtomPairEnergySuccessorTransport Atomic n bound ->
        ¬ Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n bound) := by
  intro bound
  induction bound with
  | zero =>
      intro _ hDefect
      exact
        (no_terminal_atom_projection_defect_of_no_third_sink terminal)
        hDefect
  | succ k ih =>
      intro pair_transport hDefect
      have hPrev :
          Nonempty
            (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
        atom_projection_defect_descend_of_bounded_pair_transport
          source pair_transport (Nat.lt_succ_self k) hDefect
      exact
        ih
          (boundedPairEnergySuccessorTransportRestrict
            pair_transport (Nat.le_succ k))
          hPrev

/-- Demand-level bounded transport theorem: for a target-shell demand, bounded
pair transport below that target rules out the missing-realization branch. -/
theorem not_not_atom_realization_of_demand_at_bound_by_bounded_pair_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    (terminal :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (pair_transport :
      BoundedAtomPairEnergySuccessorTransport Atomic n bound)
    (demand : RepRepairDemand SourceEvidence Residual n bound) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = bound := by
  intro hMissing
  exact
    (no_atom_projection_defect_at_bound_by_bounded_pair_transport
      terminal source bound pair_transport)
    ⟨{ demand := demand, noAtomRealization := hMissing }⟩

/-- Target-shell bounded transport theorem with a materializing terminal
no-third-sink law.  The terminal projected-repair branch is connected to an
atom-pair realization, while the positive shells are handled by bounded
pair-level successor transport. -/
theorem no_atom_projection_defect_at_bound_by_materializing_bounded_pair_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n) :
    ∀ bound : Nat,
      BoundedAtomPairEnergySuccessorTransport Atomic n bound ->
        ¬ Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n bound) :=
  no_atom_projection_defect_at_bound_by_bounded_pair_transport
    (atomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    source

/-- Demand-level target-shell bounded transport theorem with a materializing
terminal no-third-sink law. -/
theorem not_not_atom_realization_of_demand_at_bound_by_materializing_bounded_pair_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (pair_transport :
      BoundedAtomPairEnergySuccessorTransport Atomic n bound)
    (demand : RepRepairDemand SourceEvidence Residual n bound) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = bound :=
  not_not_atom_realization_of_demand_at_bound_by_bounded_pair_transport
    (atomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    source
    pair_transport
    demand

/-- Target-shell bounded transport theorem where terminal projected repair is
read through the faithful projection functor. -/
theorem no_atom_projection_defect_at_bound_by_projected_bounded_pair_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (terminal :
      AtomProjectionTerminalProjectedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n) :
    ∀ bound : Nat,
      BoundedAtomPairEnergySuccessorTransport Atomic n bound ->
        ¬ Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n bound) :=
  no_atom_projection_defect_at_bound_by_materializing_bounded_pair_transport
    (atomProjectionTerminalMaterializingNoThirdSinkOfProjected terminal)
    source

/-- Demand-level bounded transport theorem where terminal projected repair is
read through the faithful projection functor. -/
theorem not_not_atom_realization_of_demand_at_bound_by_projected_bounded_pair_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (terminal :
      AtomProjectionTerminalProjectedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (pair_transport :
      BoundedAtomPairEnergySuccessorTransport Atomic n bound)
    (demand : RepRepairDemand SourceEvidence Residual n bound) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = bound :=
  not_not_atom_realization_of_demand_at_bound_by_materializing_bounded_pair_transport
    (atomProjectionTerminalMaterializingNoThirdSinkOfProjected terminal)
    source
    pair_transport
    demand

/-- Target-shell bounded transport theorem where terminal projected repair only
asserts that the faithful partial projection is defined. -/
theorem no_atom_projection_defect_at_bound_by_defined_bounded_pair_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (terminal :
      AtomProjectionTerminalDefinedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n) :
    ∀ bound : Nat,
      BoundedAtomPairEnergySuccessorTransport Atomic n bound ->
        ¬ Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n bound) :=
  no_atom_projection_defect_at_bound_by_projected_bounded_pair_transport
    (atomProjectionTerminalProjectedNoThirdSinkOfDefined terminal)
    source

/-- Demand-level bounded transport theorem where terminal projected repair
only asserts that the faithful partial projection is defined. -/
theorem not_not_atom_realization_of_demand_at_bound_by_defined_bounded_pair_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (terminal :
      AtomProjectionTerminalDefinedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (pair_transport :
      BoundedAtomPairEnergySuccessorTransport Atomic n bound)
    (demand : RepRepairDemand SourceEvidence Residual n bound) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = bound :=
  not_not_atom_realization_of_demand_at_bound_by_projected_bounded_pair_transport
    (atomProjectionTerminalProjectedNoThirdSinkOfDefined terminal)
    source
    pair_transport
    demand

/-- Target-shell bounded transport theorem where projection failure in the
terminal projected branch would force absorbed-static. -/
theorem no_atom_projection_defect_at_bound_by_nonabsorbed_bounded_pair_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n) :
    ∀ bound : Nat,
      BoundedAtomPairEnergySuccessorTransport Atomic n bound ->
        ¬ Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n bound) :=
  no_atom_projection_defect_at_bound_by_defined_bounded_pair_transport
    (atomProjectionTerminalDefinedNoThirdSinkOfNonabsorbed terminal)
    source

/-- Demand-level bounded transport theorem where projection failure in the
terminal projected branch would force absorbed-static. -/
theorem not_not_atom_realization_of_demand_at_bound_by_nonabsorbed_bounded_pair_transport
    {Atomic : Nat -> Prop} {SourceEvidence : Type u}
    {Residual : AdditiveResidualTransportCategory SourceEvidence}
    {n bound : Nat}
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (source :
      SourceDemandOneStepDescent SourceEvidence Residual n)
    (pair_transport :
      BoundedAtomPairEnergySuccessorTransport Atomic n bound)
    (demand : RepRepairDemand SourceEvidence Residual n bound) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = bound :=
  not_not_atom_realization_of_demand_at_bound_by_defined_bounded_pair_transport
    (atomProjectionTerminalDefinedNoThirdSinkOfNonabsorbed terminal)
    source
    pair_transport
    demand


/-!
## Non-prime atom-filter toy theorem

This toy model uses the atom filter `{4, 6}`.  It is intentionally not a prime
filter.  The point is narrower: when a source residual shell is faithfully read
through a stable projection domain, a stable projection defect can be excluded
without naming prime-pair existence.
-/

namespace NonPrimeAtomFilterToy

/-- Toy arithmetic atoms: exactly the non-prime endpoint codes `4` and `6`. -/
def ToyAtom (m : Nat) : Prop :=
  m = 4 ∨ m = 6

def atom4 : MultiplicativeAtomCode ToyAtom where
  code := 4
  atomic := Or.inl rfl

def atom6 : MultiplicativeAtomCode ToyAtom where
  code := 6
  atomic := Or.inr rfl

/-- The non-prime atom pair `4 + 6 = 2 * 5`. -/
def exactPair : ArithmeticAtomPair ToyAtom 5 where
  left := atom4
  right := atom6

theorem exactPair_energy_zero :
    ArithmeticAtomPair.energy exactPair = 0 := by
  rfl

/-- Single source witness for the toy stable projection domain. -/
inductive ToySourceEvidence where
  | sourceDemand

def residualTransport :
    AdditiveResidualTransportCategory ToySourceEvidence where
  residualEnergy := fun _ => 0
  step := fun _ _ => False
  step_decreases_one := by
    intro _ _ hstep
    cases hstep

def sourceCategory :
    RepresentationFeasibleCategory ToySourceEvidence where
  feasible := fun _ => True
  path := fun _ _ => True
  path_preserves_feasible := by
    intro _ _ _ _
    trivial

def factorProduct :
    List (MultiplicativeAtomCode ToyAtom) -> Nat
  | [] => 1
  | x :: xs => x.code * factorProduct xs

def multiplicativeAtoms :
    MultiplicativeAtomFactorizationCategory ToyAtom where
  factors := fun m xs => factorProduct xs = m
  factor_product := factorProduct
  atom_factorizes_self := by
    intro a
    change a.code * 1 = a.code
    exact Nat.mul_one a.code
  factorization_reads_product := by
    intro _ _ hfactor
    exact hfactor

def projectionFunctor :
    FaithfulAtomProjectionFunctor ToyAtom ToySourceEvidence 5
      residualTransport where
  project := fun _ => some exactPair
  energy_faithful := by
    intro source _ hproject
    cases source
    cases hproject
    exact exactPair_energy_zero

def dischargeLaw :
    AtomProjectionDefectDischargeLaw ToyAtom ToySourceEvidence 5
      residualTransport sourceCategory projectionFunctor where
  defect_propagates_or_discharges := True
  finite_descent_or_holonomy_bound := True
  no_third_sink_or_naked_terminal_defect := True
  realization_of_demand := by
    intro k demand
    refine ⟨exactPair, ?_⟩
    calc
      ArithmeticAtomPair.energy exactPair =
          residualTransport.residualEnergy demand.evidence := by
        cases demand.evidence
        exact exactPair_energy_zero
      _ = k := demand.residual_eq

def stableDomain :
    StableTransportAtomProjectionDomain ToyAtom ToySourceEvidence 5 where
  multiplicative_atoms := multiplicativeAtoms
  residual_transport := residualTransport
  source_category := sourceCategory
  projection_functor := projectionFunctor
  discharge_law := dischargeLaw

/-- A concrete source demand at shell `0`, read from the toy residual transport. -/
def zeroDemand : RepRepairDemand ToySourceEvidence residualTransport 5 0 where
  evidence := ToySourceEvidence.sourceDemand
  residual_eq := rfl

/-- Concrete non-prime toy theorem: the stable projection domain forbids a
projection defect at `n = 5`, `k = 0`. -/
theorem no_nonprime_stable_projection_defect_zero :
    ¬ Nonempty
      (AtomProjectionDefect ToyAtom ToySourceEvidence
        stableDomain.residual_transport 5 0) :=
  no_stable_atom_projection_defect stableDomain

/-- The same exclusion can be read locally from the produced non-prime atom
pair, without using the stable-domain package. -/
theorem no_nonprime_projection_defect_zero_from_pair :
    ¬ Nonempty
      (AtomProjectionDefect ToyAtom ToySourceEvidence residualTransport 5 0) :=
  not_defect_of_atom_realization ⟨exactPair, exactPair_energy_zero⟩


end NonPrimeAtomFilterToy

/-!
## Uniform non-prime atom-family toy theorem

This section upgrades the single `{4, 6}` toy into a parameterized non-prime
atom filter:

`FamilyAtom m := Even m ∧ 4 ≤ m`.

For every `n ≥ 4`, the pair `(4, 2 * n - 4)` lies in the atom filter and has
zero residual energy in the fiber `2 * n`.  The stable-domain exclusion below
is still witness-return: the discharge law returns that canonical pair.  It is
not yet a transport / holonomy derivation.
-/

namespace UniformNonPrimeAtomFamily

/-- Uniform non-prime atom filter: even endpoint codes at least `4`. -/
def FamilyAtom (m : Nat) : Prop :=
  Even m ∧ 4 ≤ m

theorem two_mul_four_add_shape (t : Nat) :
    2 * (4 + t) = t + (t + 8) := by
  rw [Nat.two_mul]
  calc
    (4 + t) + (4 + t) = t + 4 + (4 + t) := by
      rw [Nat.add_comm 4 t]
    _ = t + (4 + (4 + t)) := by
      rw [Nat.add_assoc]
    _ = t + ((4 + 4) + t) := by
      rw [Nat.add_assoc 4 4 t]
    _ = t + (t + (4 + 4)) := by
      rw [Nat.add_comm (4 + 4) t]
    _ = t + (t + 8) := by
      rfl

theorem add_four_sub_four (a : Nat) :
    a + 4 - 4 = a := by
  rfl

theorem sub_four_shape (t : Nat) :
    t + (t + 8) - 4 = t + (t + 4) := by
  have h' : t + (t + 8) = t + (t + 4) + 4 := by
    calc
      t + (t + 8) = t + (t + (4 + 4)) := by
        rfl
      _ = t + ((t + 4) + 4) := by
        rw [Nat.add_assoc t 4 4]
      _ = t + (t + 4) + 4 := by
        rw [← Nat.add_assoc]
  rw [h']
  exact add_four_sub_four (t + (t + 4))

theorem split_four_shape (t : Nat) :
    t + (t + 4) = (t + 2) + (t + 2) := by
  calc
    t + (t + 4) = t + (t + (2 + 2)) := by
      rfl
    _ = t + ((t + 2) + 2) := by
      rw [Nat.add_assoc t 2 2]
    _ = (t + (t + 2)) + 2 := by
      rw [← Nat.add_assoc]
    _ = ((t + t) + 2) + 2 := by
      rw [← Nat.add_assoc t t 2]
    _ = (t + t) + (2 + 2) := by
      rw [Nat.add_assoc (t + t) 2 2]
    _ = t + (t + (2 + 2)) := by
      rw [Nat.add_assoc]
    _ = t + ((t + 2) + 2) := by
      rw [Nat.add_assoc t 2 2]
    _ = t + (2 + (t + 2)) := by
      rw [Nat.add_comm (t + 2) 2]
    _ = (t + 2) + (t + 2) := by
      rw [← Nat.add_assoc]

theorem lower_base_shape (t : Nat) :
    t + (t + 4) = 4 + (t + t) := by
  calc
    t + (t + 4) = (t + t) + 4 := by
      rw [← Nat.add_assoc]
    _ = 4 + (t + t) := by
      rw [Nat.add_comm]

theorem sum_left_shape (t : Nat) :
    4 + (t + (t + 4)) = t + (t + 8) := by
  calc
    4 + (t + (t + 4)) = (4 + t) + (t + 4) := by
      rw [Nat.add_assoc]
    _ = (t + 4) + (t + 4) := by
      rw [Nat.add_comm 4 t]
    _ = t + (4 + (t + 4)) := by
      rw [Nat.add_assoc]
    _ = t + ((4 + t) + 4) := by
      rw [Nat.add_assoc 4 t 4]
    _ = t + ((t + 4) + 4) := by
      rw [Nat.add_comm 4 t]
    _ = t + (t + (4 + 4)) := by
      rw [Nat.add_assoc t 4 4]
    _ = t + (t + 8) := by
      rfl

theorem rightCode_even_shape (t : Nat) :
    2 * (4 + t) - 4 = (t + 2) + (t + 2) := by
  have hmul : 2 * (4 + t) = t + (t + 8) :=
    two_mul_four_add_shape t
  rw [hmul]
  have hsub : t + (t + 8) - 4 = t + (t + 4) :=
    sub_four_shape t
  rw [hsub]
  exact split_four_shape t

theorem rightCode_lower_shape (t : Nat) :
    4 ≤ 2 * (4 + t) - 4 := by
  have hmul : 2 * (4 + t) = t + (t + 8) :=
    two_mul_four_add_shape t
  rw [hmul]
  have hsub : t + (t + 8) - 4 = t + (t + 4) :=
    sub_four_shape t
  rw [hsub]
  rw [lower_base_shape t]
  exact Nat.le_add_right 4 (t + t)

theorem rightCode_sum_shape (t : Nat) :
    4 + (2 * (4 + t) - 4) = 2 * (4 + t) := by
  have hright : 2 * (4 + t) - 4 = t + (t + 4) := by
    have hmul : 2 * (4 + t) = t + (t + 8) :=
      two_mul_four_add_shape t
    rw [hmul]
    exact sub_four_shape t
  rw [hright]
  rw [sum_left_shape t]
  rw [← two_mul_four_add_shape t]

theorem rightAtom_atomic (n : Nat) (hn : 4 ≤ n) :
    FamilyAtom (2 * n - 4) := by
  rcases Nat.le.dest hn with ⟨t, ht⟩
  rw [← ht]
  exact ⟨⟨t + 2, rightCode_even_shape t⟩, rightCode_lower_shape t⟩

theorem canonicalCodeSum (n : Nat) (hn : 4 ≤ n) :
    4 + (2 * n - 4) = 2 * n := by
  rcases Nat.le.dest hn with ⟨t, ht⟩
  rw [← ht]
  exact rightCode_sum_shape t

theorem subNatNat_self_zero (m : Nat) :
    Int.subNatNat m m = 0 := by
  unfold Int.subNatNat
  rw [Nat.sub_self]
  rfl

theorem intNatSubSelfZero (m : Nat) :
    ((m : Nat) : Int) - ((m : Nat) : Int) = 0 := by
  cases m with
  | zero => rfl
  | succ m =>
      change Int.subNatNat (Nat.succ m) (Nat.succ m) = 0
      exact subNatNat_self_zero (Nat.succ m)

def atom4 : MultiplicativeAtomCode FamilyAtom where
  code := 4
  atomic := ⟨⟨2, rfl⟩, Nat.le_refl 4⟩

def rightAtom (n : Nat) (hn : 4 ≤ n) :
    MultiplicativeAtomCode FamilyAtom where
  code := 2 * n - 4
  atomic := rightAtom_atomic n hn

/-- The canonical uniform pair `(4, 2 * n - 4)`. -/
def canonicalPair (n : Nat) (hn : 4 ≤ n) :
    ArithmeticAtomPair FamilyAtom n where
  left := atom4
  right := rightAtom n hn

theorem canonicalPair_left_code (n : Nat) (hn : 4 ≤ n) :
    (canonicalPair n hn).left.code = 4 := by
  rfl

theorem canonicalPair_right_code (n : Nat) (hn : 4 ≤ n) :
    (canonicalPair n hn).right.code = 2 * n - 4 := by
  rfl

theorem canonicalPair_energy_zero (n : Nat) (hn : 4 ≤ n) :
    ArithmeticAtomPair.energy (canonicalPair n hn) = 0 := by
  rw [ArithmeticAtomPair.energy, ArithmeticAtomPair.residual]
  have hsum : 4 + (2 * n - 4) = 2 * n :=
    canonicalCodeSum n hn
  change
    Int.natAbs
      (((2 * n : Nat) : Int) -
        ((4 + (2 * n - 4) : Nat) : Int)) = 0
  rw [hsum]
  rw [intNatSubSelfZero (2 * n)]
  rfl

/-- Uniform witness theorem: every fiber `2 * n` for `n ≥ 4` has a zero-energy
atom pair for the non-prime filter `Even m ∧ 4 ≤ m`. -/
theorem uniform_nonprime_atom_pair_energy_zero :
    ∀ n : Nat, 4 ≤ n ->
      ∃ p : ArithmeticAtomPair FamilyAtom n,
        ArithmeticAtomPair.energy p = 0 := by
  intro n hn
  exact ⟨canonicalPair n hn, canonicalPair_energy_zero n hn⟩

/-- One source witness type reused for each parameter `n`. -/
inductive FamilySourceEvidence where
  | sourceDemand

def residualTransport :
    AdditiveResidualTransportCategory FamilySourceEvidence where
  residualEnergy := fun _ => 0
  step := fun _ _ => False
  step_decreases_one := by
    intro _ _ hstep
    cases hstep

def sourceCategory :
    RepresentationFeasibleCategory FamilySourceEvidence where
  feasible := fun _ => True
  path := fun _ _ => True
  path_preserves_feasible := by
    intro _ _ _ _
    trivial

def factorProduct :
    List (MultiplicativeAtomCode FamilyAtom) -> Nat
  | [] => 1
  | x :: xs => x.code * factorProduct xs

def multiplicativeAtoms :
    MultiplicativeAtomFactorizationCategory FamilyAtom where
  factors := fun m xs => factorProduct xs = m
  factor_product := factorProduct
  atom_factorizes_self := by
    intro a
    change a.code * 1 = a.code
    exact Nat.mul_one a.code
  factorization_reads_product := by
    intro _ _ hfactor
    exact hfactor

def projectionFunctor (n : Nat) (hn : 4 ≤ n) :
    FaithfulAtomProjectionFunctor FamilyAtom FamilySourceEvidence n
      residualTransport where
  project := fun _ => some (canonicalPair n hn)
  energy_faithful := by
    intro source _ hproject
    cases source
    cases hproject
    exact canonicalPair_energy_zero n hn

/-- Witness-return discharge for the uniform toy family.

This is deliberately not claimed to be a transport / holonomy derivation: it
returns the canonical pair `(4, 2 * n - 4)` for the current parameter `n`. -/
def dischargeLaw (n : Nat) (hn : 4 ≤ n) :
    AtomProjectionDefectDischargeLaw FamilyAtom FamilySourceEvidence n
      residualTransport sourceCategory (projectionFunctor n hn) where
  defect_propagates_or_discharges := True
  finite_descent_or_holonomy_bound := True
  no_third_sink_or_naked_terminal_defect := True
  realization_of_demand := by
    intro k demand
    refine ⟨canonicalPair n hn, ?_⟩
    calc
      ArithmeticAtomPair.energy (canonicalPair n hn) =
          residualTransport.residualEnergy demand.evidence := by
        cases demand.evidence
        exact canonicalPair_energy_zero n hn
      _ = k := demand.residual_eq

def stableDomain (n : Nat) (hn : 4 ≤ n) :
    StableTransportAtomProjectionDomain FamilyAtom FamilySourceEvidence n where
  multiplicative_atoms := multiplicativeAtoms
  residual_transport := residualTransport
  source_category := sourceCategory
  projection_functor := projectionFunctor n hn
  discharge_law := dischargeLaw n hn

def zeroDemand (n : Nat) (_hn : 4 ≤ n) :
    RepRepairDemand FamilySourceEvidence residualTransport n 0 where
  evidence := FamilySourceEvidence.sourceDemand
  residual_eq := rfl

/-- Parameterized stable projection-defect exclusion for every `n ≥ 4`.

The result is uniform in `n`, but the current discharge law is still the
witness-return law above. -/
theorem no_uniform_nonprime_stable_projection_defect
    (n : Nat) (hn : 4 ≤ n) (k : Nat) :
    ¬ Nonempty
      (AtomProjectionDefect FamilyAtom FamilySourceEvidence
        (stableDomain n hn).residual_transport n k) :=
  no_stable_atom_projection_defect (stableDomain n hn)

/-- The zero-shell version matching the canonical pair theorem. -/
theorem no_uniform_nonprime_stable_projection_defect_zero
    (n : Nat) (hn : 4 ≤ n) :
    ¬ Nonempty
      (AtomProjectionDefect FamilyAtom FamilySourceEvidence
        (stableDomain n hn).residual_transport n 0) :=
  no_uniform_nonprime_stable_projection_defect n hn 0


end UniformNonPrimeAtomFamily


end RepresentationArithmeticAtomProjectionDefect
