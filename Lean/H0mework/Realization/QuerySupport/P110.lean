/-
  Proposition 110: the structure-determined projection supplies the canonical
  atom oracle.

  Proposition 109 still accepted a faithful Boolean atom oracle as an argument.
  In a structure-determined seven-facet system that oracle does not need to be
  an extra interpretive choice: the P94/P105 semantic projection already tells
  us how to read every primitive semantic atom.

  This file constructs the canonical projection oracle

      holdsBool a x = semanticBoolValue (project x) a

  and proves it is faithful to the system's obligation semantics.  Therefore
  the finite read-guard cost witness from P109 can be stated without an
  external oracle parameter.

  Boundary: this prices one atom read as one Boolean AST atom step, but it does
  not price the upstream work of materializing or validating the semantic
  projection itself.  That remains the P94 mechanism-faithfulness boundary.
-/

import H0mework.Realization.Relations.P109

namespace StructureDeterminedSevenFacetSystem

variable {State Prim : Type*}

/-! ## Canonical atom oracle from the semantic projection -/

/-- The canonical Boolean atom oracle induced by a structure-determined
semantic projection. -/
def projectionAtomOracle
    (S : StructureDeterminedSevenFacetSystem State) :
    BoolObligationOracle S.obligations where
  holdsBool := fun a x =>
    semanticBoolValue (S.pullback.projection.project x) a
  holdsBool_iff := by
    intro a x
    calc
      semanticBoolValue (S.pullback.projection.project x) a = true <->
          (semanticObligationSemantics semanticBoolPredicates).holds a
            (S.pullback.projection.project x) :=
        (semanticBoolHolds_iff_value
          (S.pullback.projection.project x) a).symm
      _ <-> S.obligations.holds a x :=
        (S.pullback.projection.atom_iff x a).symm

/-- THEOREM 1: the canonical oracle is definitionally the projection reader. -/
theorem projectionAtomOracle_holdsBool_eq
    (S : StructureDeterminedSevenFacetSystem State)
    (a : SemanticAtom) (x : State) :
    (S.projectionAtomOracle).holdsBool a x =
      semanticBoolValue (S.pullback.projection.project x) a :=
  rfl

/-- THEOREM 2: the canonical oracle agrees with Prop-valued obligation
semantics for every Boolean query. -/
theorem projectionAtomOracle_evalBool_iff_eval
    (S : StructureDeterminedSevenFacetSystem State)
    (q : BoolQuery SemanticAtom) (x : State) :
    BoolQuery.evalBool S.projectionAtomOracle.holdsBool q x = true <->
      BoolQuery.eval S.obligations q x :=
  BoolQuery.evalBool_iff_eval S.projectionAtomOracle q x

/-- THEOREM 3: Boolean query evaluation through the canonical projection oracle
costs exactly the query AST node count. -/
theorem projectionAtomOracle_evalBoolWithCost_cost_eq_nodeCount
    (S : StructureDeterminedSevenFacetSystem State)
    (q : BoolQuery SemanticAtom) (x : State) :
    (BoolQuery.evalBoolWithCost S.projectionAtomOracle.holdsBool q x).2 =
      BoolQuery.nodeCount q :=
  BoolQuery.evalBoolWithCost_cost_eq_nodeCount
    S.projectionAtomOracle.holdsBool q x

/-- THEOREM 4: two structure-determined systems with the same semantic
projection induce the same canonical atom oracle. -/
theorem projectionAtomOracle_eq_of_projection_eq
    (S T : StructureDeterminedSevenFacetSystem State)
    (hproj :
      forall x,
        S.pullback.projection.project x =
          T.pullback.projection.project x)
    (a : SemanticAtom) (x : State) :
    S.projectionAtomOracle.holdsBool a x =
      T.projectionAtomOracle.holdsBool a x := by
  simp [projectionAtomOracle, hproj x]

/-! ## Read-guard witness without an external oracle argument -/

/-- THEOREM 5: every projection-visible predicate has a finite read-guard
cost witness using the canonical projection atom oracle. -/
theorem projectionVisible_canonicalFiniteReadGuardCostWitness
    (S : StructureDeterminedSevenFacetSystem State)
    (target : State -> Prop)
    (hvisible : ProjectionVisible S target) :
    exists q : BoolQuery SemanticAtom,
      exists plan : FiniteStatefulGenAlg State Unit Prim,
        (forall x, BoolQuery.eval S.obligations q x <-> target x) /\
        (forall [DecidableEq State]
          (stateDomain : Finset State) (rowDomain : Finset Unit)
          (env : Prim -> State -> Finset (Unit × State))
          (x : State) (row : Unit) (y : State),
          (row, y) ∈
              FiniteStatefulGenAlg.evalFinset stateDomain rowDomain env
                plan x <->
            target x /\ row = () /\ y = x) /\
        (forall [DecidableEq State]
          (stateDomain : Finset State) (rowDomain : Finset Unit)
          (env : Prim -> State -> Finset (Unit × State))
          (x : State),
          (FiniteStatefulGenAlg.evalWithCost stateDomain rowDomain env
              plan x).2 = 1) /\
        (forall x,
          (BoolQuery.evalBoolWithCost S.projectionAtomOracle.holdsBool q x).2 =
            BoolQuery.nodeCount q) :=
  S.projectionVisible_finiteReadGuardCostWitness
    target hvisible S.projectionAtomOracle

/-!
  Summary:
  - The P94/P105 semantic projection induces a canonical Boolean atom oracle.
  - The oracle is faithful to the system's obligation semantics and has no
    additional interpretive freedom once the projection is fixed.
  - Projection-visible read-guard cost witnesses therefore no longer need an
    externally supplied atom oracle; only projection materialization remains
    outside the theorem.
-/


end StructureDeterminedSevenFacetSystem
