/-
  Proposition 79: workload and shared-cost bounds for finite stateful queries.

  Proposition 78 closes one finite stateful query: executable result,
  Prop-valued stateful algebra/calculus denotation, and P74 structural cost.

  This file lifts that one-query result to finite agent workloads.  A workload
  is a list of `(query, currentState)` pairs.  The current state affects the
  actual executable result, but the structural `workBound` is query-shaped and
  state-independent, so a whole workload is bounded by:

      sum per-query workBound
      <= query_count * max_per_query_workBound

  Adding one shared materialization/cache-fill cost gives the same
  division-free amortized shape as Proposition 62, now for the stateful
  read/generate/write query algebra.
-/

import H0mework.Realization.QueryPlans.P78

/-! ## Finite stateful workloads -/

/-- A finite stateful workload item: run query `q` at current state `x`. -/
abbrev FiniteStatefulWorkItem (State Row Prim : Type*) :=
  FiniteStatefulGenAlg State Row Prim × State

/-- Total executable cost for a list of finite stateful query runs. -/
def finiteStatefulWorkloadTotalCost
    {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State)) :
    List (FiniteStatefulWorkItem State Row Prim) -> Nat
  | [] => 0
  | item :: rest =>
      (FiniteStatefulGenAlg.evalWithCost stateDomain rowDomain env
        item.1 item.2).2 +
          finiteStatefulWorkloadTotalCost stateDomain rowDomain env rest

/-- Sum of structural work bounds for a finite stateful workload. -/
def finiteStatefulWorkloadTotalBound
    {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row) :
    List (FiniteStatefulWorkItem State Row Prim) -> Nat
  | [] => 0
  | item :: rest =>
      FiniteStatefulGenAlg.workBound stateDomain rowDomain item.1 +
        finiteStatefulWorkloadTotalBound stateDomain rowDomain rest

/-- Maximum structural per-query bound in a finite stateful workload. -/
def finiteStatefulWorkloadMaxBound
    {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row) :
    List (FiniteStatefulWorkItem State Row Prim) -> Nat
  | [] => 0
  | item :: rest =>
      Nat.max
        (FiniteStatefulGenAlg.workBound stateDomain rowDomain item.1)
        (finiteStatefulWorkloadMaxBound stateDomain rowDomain rest)

/-- THEOREM 1: finite stateful workload executable cost is bounded by the sum
of per-query structural bounds. -/
theorem finiteStatefulWorkloadTotalCost_le_totalBound
    {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State))
    (hEnv :
      forall p x,
        env p x ⊆ FiniteStatefulGenAlg.pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain) :
    forall qs : List (FiniteStatefulWorkItem State Row Prim),
      finiteStatefulWorkloadTotalCost stateDomain rowDomain env qs ≤
        finiteStatefulWorkloadTotalBound stateDomain rowDomain qs := by
  intro qs
  induction qs with
  | nil =>
      simp [finiteStatefulWorkloadTotalCost,
        finiteStatefulWorkloadTotalBound]
  | cons item rest ih =>
      have hq :
          (FiniteStatefulGenAlg.evalWithCost stateDomain rowDomain env
            item.1 item.2).2 ≤
          FiniteStatefulGenAlg.workBound stateDomain rowDomain item.1 :=
        FiniteStatefulGenAlg.evalWithCost_cost_le_workBound stateDomain
          rowDomain env hEnv hRow hCurrent item.1 item.2
      simp [finiteStatefulWorkloadTotalCost,
        finiteStatefulWorkloadTotalBound]
      omega

/-- THEOREM 2: the sum of per-query stateful bounds is bounded by
`query_count * max_per_query_bound`. -/
theorem finiteStatefulWorkloadTotalBound_le_length_mul_maxBound
    {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row) :
    forall qs : List (FiniteStatefulWorkItem State Row Prim),
      finiteStatefulWorkloadTotalBound stateDomain rowDomain qs ≤
        qs.length * finiteStatefulWorkloadMaxBound stateDomain rowDomain qs := by
  intro qs
  induction qs with
  | nil =>
      simp [finiteStatefulWorkloadTotalBound,
        finiteStatefulWorkloadMaxBound]
  | cons item rest ih =>
      let b := FiniteStatefulGenAlg.workBound stateDomain rowDomain item.1
      let m := finiteStatefulWorkloadMaxBound stateDomain rowDomain rest
      have hhead : b ≤ Nat.max b m := Nat.le_max_left b m
      have htail :
          finiteStatefulWorkloadTotalBound stateDomain rowDomain rest ≤
            rest.length * m := ih
      have htail' :
          finiteStatefulWorkloadTotalBound stateDomain rowDomain rest ≤
            rest.length * Nat.max b m := by
        exact le_trans htail
          (Nat.mul_le_mul_left rest.length (Nat.le_max_right b m))
      dsimp [finiteStatefulWorkloadTotalBound,
        finiteStatefulWorkloadMaxBound]
      calc
        b + finiteStatefulWorkloadTotalBound stateDomain rowDomain rest
            ≤ Nat.max b m + rest.length * Nat.max b m := by
              exact Nat.add_le_add hhead htail'
        _ = Nat.succ rest.length * Nat.max b m := by
              rw [Nat.succ_mul]
              omega

/-- THEOREM 3: executable finite stateful workload cost is bounded by
`query_count * max_per_query_bound`. -/
theorem finiteStatefulWorkloadTotalCost_le_length_mul_maxBound
    {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State))
    (hEnv :
      forall p x,
        env p x ⊆ FiniteStatefulGenAlg.pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain)
    (qs : List (FiniteStatefulWorkItem State Row Prim)) :
    finiteStatefulWorkloadTotalCost stateDomain rowDomain env qs ≤
      qs.length * finiteStatefulWorkloadMaxBound stateDomain rowDomain qs := by
  exact le_trans
    (finiteStatefulWorkloadTotalCost_le_totalBound
      stateDomain rowDomain env hEnv hRow hCurrent qs)
    (finiteStatefulWorkloadTotalBound_le_length_mul_maxBound
      stateDomain rowDomain qs)

/-! ## Shared materialization / cache-fill budget -/

/-- Total finite stateful workload cost after one shared materialization or
cache-fill charge. -/
def finiteStatefulSharedWorkloadTotalCost
    {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (sharedCost : Nat)
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State))
    (qs : List (FiniteStatefulWorkItem State Row Prim)) : Nat :=
  sharedCost + finiteStatefulWorkloadTotalCost stateDomain rowDomain env qs

/-- Division-free amortized bound for a finite stateful workload. -/
def finiteStatefulSharedWorkloadAmortizedBound
    {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (sharedCost : Nat)
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (qs : List (FiniteStatefulWorkItem State Row Prim)) : Nat :=
  sharedCost + qs.length *
    finiteStatefulWorkloadMaxBound stateDomain rowDomain qs

/-- THEOREM 4: after one shared charge, the finite stateful workload is bounded
by the division-free amortized expression. -/
theorem finiteStatefulSharedWorkloadTotalCost_le_amortizedBound
    {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (sharedCost : Nat)
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State))
    (hEnv :
      forall p x,
        env p x ⊆ FiniteStatefulGenAlg.pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain)
    (qs : List (FiniteStatefulWorkItem State Row Prim)) :
    finiteStatefulSharedWorkloadTotalCost sharedCost stateDomain rowDomain env qs ≤
      finiteStatefulSharedWorkloadAmortizedBound sharedCost stateDomain
        rowDomain qs := by
  have h :=
    finiteStatefulWorkloadTotalCost_le_length_mul_maxBound
      stateDomain rowDomain env hEnv hRow hCurrent qs
  simp [finiteStatefulSharedWorkloadTotalCost,
    finiteStatefulSharedWorkloadAmortizedBound]
  omega

/-- Packaged cost certificate for a finite stateful workload. -/
structure FiniteStatefulWorkloadCostCertificate
    {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (sharedCost : Nat)
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State))
    (qs : List (FiniteStatefulWorkItem State Row Prim)) where
  totalCost_le_totalBound :
    finiteStatefulWorkloadTotalCost stateDomain rowDomain env qs ≤
      finiteStatefulWorkloadTotalBound stateDomain rowDomain qs
  totalBound_le_length_mul_max :
    finiteStatefulWorkloadTotalBound stateDomain rowDomain qs ≤
      qs.length * finiteStatefulWorkloadMaxBound stateDomain rowDomain qs
  totalCost_le_length_mul_max :
    finiteStatefulWorkloadTotalCost stateDomain rowDomain env qs ≤
      qs.length * finiteStatefulWorkloadMaxBound stateDomain rowDomain qs
  sharedCost_le_amortizedBound :
    finiteStatefulSharedWorkloadTotalCost sharedCost stateDomain rowDomain env qs ≤
      finiteStatefulSharedWorkloadAmortizedBound sharedCost stateDomain
        rowDomain qs

/-- THEOREM 5: every finite stateful workload has a cost certificate once the
finite domains cover primitives, returned rows, and current states. -/
theorem finiteStatefulWorkloadCostCertificate
    {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (sharedCost : Nat)
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State))
    (hEnv :
      forall p x,
        env p x ⊆ FiniteStatefulGenAlg.pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain)
    (qs : List (FiniteStatefulWorkItem State Row Prim)) :
    FiniteStatefulWorkloadCostCertificate sharedCost stateDomain rowDomain
      env qs where
  totalCost_le_totalBound :=
    finiteStatefulWorkloadTotalCost_le_totalBound
      stateDomain rowDomain env hEnv hRow hCurrent qs
  totalBound_le_length_mul_max :=
    finiteStatefulWorkloadTotalBound_le_length_mul_maxBound
      stateDomain rowDomain qs
  totalCost_le_length_mul_max :=
    finiteStatefulWorkloadTotalCost_le_length_mul_maxBound
      stateDomain rowDomain env hEnv hRow hCurrent qs
  sharedCost_le_amortizedBound :=
    finiteStatefulSharedWorkloadTotalCost_le_amortizedBound
      sharedCost stateDomain rowDomain env hEnv hRow hCurrent qs

/-!
  Summary:
  - Finite stateful query workloads inherit the single-query P74 structural
    bound query-by-query.
  - The total workload is bounded by the sum of per-query `workBound`s, then by
    `query_count * max_per_query_workBound`.
  - A shared materialization/cache-fill charge yields a division-free amortized
    workload certificate for the stateful read/generate/write query algebra.

  Remaining boundary:
  - No cache replacement policy or probabilistic average-case model is proved.
  - Source reopen, external model generation, and finite-domain materialization
    remain explicit shared/external costs rather than hidden assumptions.
-/
