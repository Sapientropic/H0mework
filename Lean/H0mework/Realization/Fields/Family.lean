/-
  Proposition 65: gluing failure is recollection-producing memory.

  Proposition 64 built the local pullback:

      field-boundary support ×_{temporal holonomy} recollection activation

  This file globalizes the slogan at the current Prop-valued descent level.
  For locally convergent pieces, a glued global section fails exactly when
  there exists a chosen field-boundary activation in the P64 pullback.  That
  activation installs future trace through the recollection bridge.

  This is the first Lean theorem in this line that directly states the memory
  axiom:

      gluing failure iff memory/recollection activation

  Boundary: this is still over the P58/P60 Prop-valued descent skeleton and
  requires a P63/P64 mechanism bridge.  It is not yet a cohomology quotient or
  a theorem that every runtime automatically supplies the bridge.
-/

import H0mework.Realization.Fields.BoundaryPredicates

namespace FieldHolonomyRecollectionBridge

variable {Left Right Global Field Event Time State Observation ActAtom
    TraceAtom : Type*}
variable {FL : FieldFamily Left Field} {FR : FieldFamily Right Field}
variable {FG : FieldFamily Global Field} {glue : Left -> Right -> Global}

/-! ## Generic field families -/

/-- THEOREM 1: when both local pieces converge, global gluing failure is
exactly nonempty P64 boundary activation. -/
theorem chosenFieldBoundaryActivation_nonempty_iff_global_failed
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (l : Left) (r : Right)
    (hl : FieldConvergence FL l) (hr : FieldConvergence FR r) :
    (exists field, ChosenFieldBoundaryActivation B l r field) <->
      Not (FieldConvergence FG (glue l r)) := by
  constructor
  · rintro ⟨field, hactivation⟩
    have hhol : FieldBoundaryHolonomy FL FR FG glue l r field :=
      (chosenFieldBoundaryActivation_iff_boundaryHolonomy B l r field).mp
        hactivation
    exact (fieldBoundaryHolonomy_nonempty_iff_local_convergent_global_failed
      FL FR FG glue l r hl hr).mp ⟨field, hhol⟩
  · intro hfail
    rcases (fieldBoundaryHolonomy_nonempty_iff_local_convergent_global_failed
      FL FR FG glue l r hl hr).mpr hfail with ⟨field, hhol⟩
    exact ⟨field,
      (chosenFieldBoundaryActivation_iff_boundaryHolonomy B l r field).mpr
        hhol⟩

/-- THEOREM 2: a global gluing failure installs future trace through some
field-boundary activation. -/
theorem globalGluingFailure_installs_trace
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (l : Left) (r : Right)
    (hl : FieldConvergence FL l) (hr : FieldConvergence FR r)
    (hfail : Not (FieldConvergence FG (glue l r))) :
    exists field,
      TemporalTracePotential
        (B.temporal.stepOf (B.events.eventOf l r field)) := by
  rcases (chosenFieldBoundaryActivation_nonempty_iff_global_failed
    B l r hl hr).mpr hfail with ⟨field, hactivation⟩
  exact ⟨field,
    chosenFieldBoundaryActivation_installs_trace B l r field hactivation⟩

/-! ## Semantic AIppocampus fields -/

/-- THEOREM 3: for the seven semantic fields, local `C_safe` plus global
`¬ C_safe` is exactly nonempty boundary activation. -/
theorem semanticChosenActivation_nonempty_iff_global_unsafe
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    {Event Time State Observation ActAtom TraceAtom : Type*}
    (B :
      FieldHolonomyRecollectionBridge
        (semanticFieldFamily PL) (semanticFieldFamily PR)
        (semanticFieldFamily PG) glue Event Time State Observation ActAtom
        TraceAtom)
    (l : Left) (r : Right)
    (hl : CSafe PL l) (hr : CSafe PR r) :
    (exists field, ChosenFieldBoundaryActivation B l r field) <->
      Not (CSafe PG (glue l r)) := by
  calc
    (exists field, ChosenFieldBoundaryActivation B l r field) <->
        Not (FieldConvergence (semanticFieldFamily PG) (glue l r)) :=
      chosenFieldBoundaryActivation_nonempty_iff_global_failed
        B l r
        ((semanticFieldConvergence_iff_csafe PL l).mpr hl)
        ((semanticFieldConvergence_iff_csafe PR r).mpr hr)
    _ <-> Not (CSafe PG (glue l r)) :=
      not_congr (semanticFieldConvergence_iff_csafe PG (glue l r))

/-- THEOREM 4: for the seven semantic fields, a global `C_safe` failure after
locally safe gluing installs future trace through some semantic field
activation. -/
theorem semanticGlobalUnsafe_installs_trace
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    {Event Time State Observation ActAtom TraceAtom : Type*}
    (B :
      FieldHolonomyRecollectionBridge
        (semanticFieldFamily PL) (semanticFieldFamily PR)
        (semanticFieldFamily PG) glue Event Time State Observation ActAtom
        TraceAtom)
    (l : Left) (r : Right)
    (hl : CSafe PL l) (hr : CSafe PR r)
    (hfail : Not (CSafe PG (glue l r))) :
    exists field,
      TemporalTracePotential
        (B.temporal.stepOf (B.events.eventOf l r field)) := by
  have hfieldFail :
      Not (FieldConvergence (semanticFieldFamily PG) (glue l r)) :=
    (not_congr (semanticFieldConvergence_iff_csafe PG (glue l r))).mpr
      hfail
  exact globalGluingFailure_installs_trace B l r
    ((semanticFieldConvergence_iff_csafe PL l).mpr hl)
    ((semanticFieldConvergence_iff_csafe PR r).mpr hr)
    hfieldFail

end FieldHolonomyRecollectionBridge

/-! ## Two-point witness -/

/-- THEOREM 5: in the two-point witness, global field failure is exactly
nonempty chosen activation. -/
theorem twoPoint_activation_nonempty_iff_global_failed :
    (exists field,
      FieldHolonomyRecollectionBridge.ChosenFieldBoundaryActivation
        twoPointFieldHolonomyRecollectionBridge
        TwoPointLocalSection.localSafe TwoPointLocalSection.localSafe field) <->
      Not (FieldConvergence twoPointGlobalFieldFamily
        (twoPointFieldGlue TwoPointLocalSection.localSafe
          TwoPointLocalSection.localSafe)) := by
  exact FieldHolonomyRecollectionBridge.chosenFieldBoundaryActivation_nonempty_iff_global_failed
      twoPointFieldHolonomyRecollectionBridge
      TwoPointLocalSection.localSafe TwoPointLocalSection.localSafe
      (fun field => trivial)
      (fun field => trivial)

/-- THEOREM 6: the two-point global gluing failure installs future trace via
the global theorem, not only by the hand-picked active event theorem. -/
theorem twoPoint_globalGluingFailure_installs_trace :
    exists field,
      TemporalTracePotential
        (twoPointFieldHolonomyRecollectionBridge.temporal.stepOf
          (twoPointFieldHolonomyRecollectionBridge.events.eventOf
            TwoPointLocalSection.localSafe TwoPointLocalSection.localSafe
            field)) := by
  have hfail :
      Not (FieldConvergence twoPointGlobalFieldFamily
        (twoPointFieldGlue TwoPointLocalSection.localSafe
          TwoPointLocalSection.localSafe)) := by
    intro hconv
    exact hconv TwoPointMemoryFieldAtom.holonomyField
  exact FieldHolonomyRecollectionBridge.globalGluingFailure_installs_trace
    twoPointFieldHolonomyRecollectionBridge
    TwoPointLocalSection.localSafe TwoPointLocalSection.localSafe
    (fun field => trivial)
    (fun field => trivial)
    hfail

/-!
  Summary:
  - `chosenFieldBoundaryActivation_nonempty_iff_global_failed` is the direct
    Lean form of "gluing failure iff memory/recollection activation" for the
    current Prop-valued field geometry.
  - `semanticChosenActivation_nonempty_iff_global_unsafe` specializes that
    theorem to the seven AIppocampus safety fields: locally `C_safe` pieces
    that glue into global `¬ C_safe` produce a semantic field activation.
  - `globalGluingFailure_installs_trace` and its semantic version prove that
    the activation is not inert: it installs future trace through recollection.
-/
