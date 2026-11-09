import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Sequential

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Same

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

variable {law : DebtActivationLaw} {joint : WorldRelationNetwork}
  {source target : Root.Cut Party Good Port Technology Instrument}
  {shape : Shape law source.native.frame.N joint} {phase future : law.DebtState}
  {wait : law.TransportAt phase phase}
  (current : Resident shape phase wait) (edge : History.NativeEdge source target)
  (motion : Motion law phase future)

abbrev afterShape : Shape law target.native.frame.N joint := edge.sameNetwork.symm ▸ shape

private theorem support_cast {N M J : WorldRelationNetwork} {R : DebtActivationLaw}
    (shape : Shape R N J) (same : M = N) (support : M.Support) (state : R.DebtState) :
    (same.symm ▸ shape : Shape R M J).support support state = shape.support (same ▸ support) state := by
  cases same
  rfl

private theorem repair_cast {N M J : WorldRelationNetwork} {R : DebtActivationLaw}
    (shape : Shape R N J) (same : M = N) (support : M.Support) (state : R.DebtState) :
    HEq ((same.symm ▸ shape : Shape R M J).repair support state) (shape.repair (same ▸ support) state) := by
  cases same
  rfl

def lifted : Whole joint (shape.support (sourceSupport source.native) phase)
    (shape.support (edge.sameNetwork ▸ sourceSupport target.native) future) :=
  let owner := source.native.frame.entry source.native.visit.current
  ⟨shape.lift motion edge.whole owner, shape.lift_keeps_keys _ _ _ edge.keys⟩

def frame : Frame target.native (afterShape (shape := shape) edge) future where
  initialSupport := current.support
  initialFinite := current.finite
  initialWrite := (lifted edge motion).rebase current.support_eq.symm
    (support_cast shape edge.sameNetwork (sourceSupport target.native) future).symm
  writes := edge.writes || match motion with
    | .inl _ => true
    | .inr _ => false

theorem repair_written :
    ((frame current edge motion).initialWrite.val.destination
      (Sequential.translatedEntry current (frame current edge motion) rfl)).1 =
    (afterShape (shape := shape) edge).repair (sourceSupport target.native) future := by
  let destination := edge.sameNetwork ▸ sourceSupport target.native
  have equal := support_cast shape edge.sameNetwork (sourceSupport target.native) future
  have wrote := destination_congr current.support_eq equal (frame current edge motion).initialWrite.val
    (lifted edge motion).val (Whole.rebase_destination current.support_eq.symm equal.symm (lifted edge motion))
    current.entry (shape.repair (sourceSupport source.native) phase) current.repair_eq
  have repair : ((lifted edge motion).val.destination (shape.repair (sourceSupport source.native) phase)).1 =
      shape.repair destination future := shape.lift_destination_repair _ _ _
  exact eq_of_heq (wrote.trans ((heq_of_eq repair).trans
    (repair_cast shape edge.sameNetwork (sourceSupport target.native) future).symm))

variable (waiting : law.TransportAt future future)

def landed : Resident (native := target.native) (afterShape (shape := shape) edge) future waiting :=
  (frame current edge motion).resident waiting
    (Frame.inherit current (frame current edge motion) waiting)
    (Sequential.translatedEntry current (frame current edge motion) rfl)
    (repair_written current edge motion)

abbrev generated (balance : ℚ) :=
  Sequential.generated current (frame current edge motion) waiting rfl balance

theorem actual_write_generates_the_next_resident (balance : ℚ) :
    (⟨joint, (generated current edge motion waiting balance).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = (landed current edge motion waiting).erase :=
  Sequential.generated_enters_the_actual_frame current (frame current edge motion) waiting rfl balance
    (repair_written current edge motion)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Same
