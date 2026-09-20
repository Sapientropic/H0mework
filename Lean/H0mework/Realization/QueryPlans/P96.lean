/-
  Proposition 96: named AIppocampus runtime generators inherit query
  completeness and finite stateful cost certificates.

  Propositions 61, 73, 78, and 79 already prove the important abstract facts:
  covered runtime generative plans are mutually expressive with the
  Kleisli/generative algebra and range-restricted calculus, and finite stateful
  read/generate/write plans have explicit structural cost bounds.

  This file closes the next mechanism-faithfulness seam for the current
  AIppocampus formal harness.  The runtime surfaces named in the architecture
  discussion -- score fusion, authority, and gluing -- are made into one finite
  primitive generator basis.  Once each named surface supplies its declared
  relation / finite transition coverage, the existing completeness and cost
  theorems apply to every plan over that basis.

  Boundary: the theorem is still relative to the coverage certificate.  It does
  not prove that production score fusion, authority checks, or gluing probes are
  correct by name alone; it says there is no additional query-algebra debt after
  those three mechanism certificates are supplied.
-/

import H0mework.Realization.QuerySupport.P61
import H0mework.Realization.QueryPlans.P79

/-! ## The current AIppocampus named generator basis -/

/-- The three runtime generator surfaces currently exposed by the formal
harness: score fusion, authority, and gluing. -/
inductive AippocampusRuntimeGenerator where
  | scoreFusion
  | authority
  | gluing
  deriving DecidableEq, Repr

namespace AippocampusRuntimeGenerator

/-- The finite universe of named AIppocampus runtime generators. -/
def generatorUniverse : Finset AippocampusRuntimeGenerator :=
  {scoreFusion, authority, gluing}

/-- THEOREM 1: the named-generator universe contains every constructor. -/
theorem mem_generatorUniverse (g : AippocampusRuntimeGenerator) :
    g ∈ generatorUniverse := by
  cases g <;> simp [generatorUniverse]

/-- THEOREM 2: the named-generator basis has exactly the three declared cases.
-/
theorem cases_complete (g : AippocampusRuntimeGenerator) :
    g = scoreFusion \/ g = authority \/ g = gluing := by
  cases g
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end AippocampusRuntimeGenerator

/-! ## Per-surface coverage as a runtime generator coverage certificate -/

/-- A mechanism-faithfulness certificate for the three named runtime
generators.  Each runtime surface must be represented by a declared field
relation.  The fields are per-surface on purpose: missing one of the three
runtime surfaces leaves the bridge unapplied rather than silently treating it
as covered. -/
structure AippocampusNamedGeneratorCoverage (Declared Row : Type*) where
  scoreFusionDeclared : Declared
  authorityDeclared : Declared
  gluingDeclared : Declared
  runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Prop
  declaredRel : Declared -> Row -> Row -> Prop
  scoreFusion_covers :
    forall source target,
      declaredRel scoreFusionDeclared source target <->
        runtimeRel AippocampusRuntimeGenerator.scoreFusion source target
  authority_covers :
    forall source target,
      declaredRel authorityDeclared source target <->
        runtimeRel AippocampusRuntimeGenerator.authority source target
  gluing_covers :
    forall source target,
      declaredRel gluingDeclared source target <->
        runtimeRel AippocampusRuntimeGenerator.gluing source target

namespace AippocampusNamedGeneratorCoverage

variable {Declared Row Base State : Type*}

/-- Map each runtime generator name to the declared relation that covers it. -/
def toDeclared (C : AippocampusNamedGeneratorCoverage Declared Row) :
    AippocampusRuntimeGenerator -> Declared
  | AippocampusRuntimeGenerator.scoreFusion => C.scoreFusionDeclared
  | AippocampusRuntimeGenerator.authority => C.authorityDeclared
  | AippocampusRuntimeGenerator.gluing => C.gluingDeclared

/-- THEOREM 3: per-surface coverage is exactly a P38
`RuntimeGeneratorCoverage` certificate. -/
def toRuntimeGeneratorCoverage
    (C : AippocampusNamedGeneratorCoverage Declared Row) :
    RuntimeGeneratorCoverage AippocampusRuntimeGenerator Declared Row where
  toDeclared := C.toDeclared
  runtimeRel := C.runtimeRel
  declaredRel := C.declaredRel
  covers := by
    intro generator source target
    cases generator
    · exact C.scoreFusion_covers source target
    · exact C.authority_covers source target
    · exact C.gluing_covers source target

/-- THEOREM 4: every runtime plan over the named AIppocampus generator basis
has a three-way runtime/Kleisli/calculus equivalence once the three surfaces
are covered. -/
def runtimePlanGenerativeQueryEquivalence
    (C : AippocampusNamedGeneratorCoverage Declared Row)
    (env : Base -> Row -> Prop)
    (q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator) :
    GenerativeQueryEquivalence env C.runtimeRel :=
  coveredRuntimePlanGenerativeQueryEquivalence
    C.toRuntimeGeneratorCoverage env q

/-- THEOREM 5: over the named AIppocampus generator basis, covered runtime
plans, the Kleisli/generative algebra, and the range-restricted calculus are
mutually expressive. -/
theorem named_runtime_kleisli_calc_mutual_completeness
    (C : AippocampusNamedGeneratorCoverage Declared Row)
    (env : Base -> Row -> Prop) :
    (forall q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
      exists alg : KleisliFieldAlg Row Base,
        forall row,
          KleisliFieldAlg.eval env alg row <->
            RuntimeGenerativePlan.eval env C.runtimeRel q row) /\
    (forall alg : KleisliFieldAlg Row Base,
      exists q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
        forall row,
          RuntimeGenerativePlan.eval env C.runtimeRel q row <->
            KleisliFieldAlg.eval env alg row) /\
    (forall q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
      exists formula : KleisliFieldCalc Row Base,
        forall row,
          KleisliFieldCalc.eval env formula row <->
            RuntimeGenerativePlan.eval env C.runtimeRel q row) /\
    (forall formula : KleisliFieldCalc Row Base,
      exists q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
        forall row,
          RuntimeGenerativePlan.eval env C.runtimeRel q row <->
            KleisliFieldCalc.eval env formula row) := by
  exact covered_runtime_kleisli_calc_mutual_completeness
    C.toRuntimeGeneratorCoverage env

/-- THEOREM 6: runtime -> Kleisli -> runtime roundtrip is sound for every
covered plan over the named AIppocampus generator basis. -/
theorem named_runtime_kleisli_runtime_roundtrip_sound
    (C : AippocampusNamedGeneratorCoverage Declared Row)
    (env : Base -> Row -> Prop)
    (q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator)
    (row : Row) :
    RuntimeGenerativePlan.eval env C.runtimeRel
        (kleisliAlgToRuntimePlan
        (runtimePlanToKleisli C.toRuntimeGeneratorCoverage q)) row <->
      RuntimeGenerativePlan.eval env C.runtimeRel q row := by
  exact _root_.runtime_kleisli_runtime_roundtrip_sound
    C.toRuntimeGeneratorCoverage env q row

end AippocampusNamedGeneratorCoverage

/-! ## Finite stateful cost certificates over the same named basis -/

/-- THEOREM 7: every finite stateful query over the named AIppocampus
generator basis has a denotation/calculus/cost certificate when its finite
transition environment is domain-covered. -/
def namedFiniteStatefulCompletenessCostCertificate
    {State Row : Type*} [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : AippocampusRuntimeGenerator -> State -> Finset (Row × State))
    (hEnv :
      forall p x,
        env p x ⊆ FiniteStatefulGenAlg.pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain)
    (q : FiniteStatefulGenAlg State Row AippocampusRuntimeGenerator) :
    FiniteStatefulCompletenessCostCertificate stateDomain rowDomain env q :=
  finiteStatefulCompletenessCostCertificate
    stateDomain rowDomain env hEnv hRow hCurrent q

/-- THEOREM 8: the executable cost of a finite stateful named-generator query
is bounded by its structural `workBound`. -/
theorem namedFiniteStateful_cost_le_workBound
    {State Row : Type*} [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : AippocampusRuntimeGenerator -> State -> Finset (Row × State))
    (hEnv :
      forall p x,
        env p x ⊆ FiniteStatefulGenAlg.pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain)
    (q : FiniteStatefulGenAlg State Row AippocampusRuntimeGenerator)
    (x : State) :
    (FiniteStatefulGenAlg.evalWithCost stateDomain rowDomain env q x).2 ≤
      FiniteStatefulGenAlg.workBound stateDomain rowDomain q := by
  exact FiniteStatefulGenAlg.evalWithCost_cost_le_workBound
    stateDomain rowDomain env hEnv hRow hCurrent q x

/-- THEOREM 9: finite workloads of named-generator stateful queries inherit the
division-free amortized structural bound. -/
theorem namedFiniteStatefulWorkloadCostCertificate
    {State Row : Type*} [DecidableEq State] [DecidableEq Row]
    (sharedCost : Nat)
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : AippocampusRuntimeGenerator -> State -> Finset (Row × State))
    (hEnv :
      forall p x,
        env p x ⊆ FiniteStatefulGenAlg.pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain)
    (qs : List (FiniteStatefulWorkItem State Row AippocampusRuntimeGenerator)) :
    FiniteStatefulWorkloadCostCertificate sharedCost stateDomain rowDomain
      env qs := by
  exact finiteStatefulWorkloadCostCertificate
    sharedCost stateDomain rowDomain env hEnv hRow hCurrent qs

/-!
  Summary:
  - `AippocampusRuntimeGenerator` makes the current score_fusion / authority /
    gluing runtime surfaces a finite named primitive basis.
  - Per-surface coverage is enough to reuse P61's Codd-style
    runtime/Kleisli/calculus completeness theorem.
  - Finite stateful plans over the same named basis reuse P78/P79's
    completeness and workload cost certificates.

  Remaining boundary:
  - The runtime still owes concrete coverage evidence for the three surfaces.
  - Source reopen, external model calls, cache fill, and domain materialization
    remain external/shared costs; they are not hidden inside the query algebra.
-/
