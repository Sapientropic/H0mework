import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.Coverage

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def writePointContext {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : SourceNativeSource N V) :
    WriteContext source ≃ Σ point : Point source, Σ target : N.Support,
      OpenResponsibilityAt N point.2.1 × OpenResponsibilityAt N target where
  toFun := fun ⟨current, event, target, a, b⟩ => ⟨⟨current, event⟩, target, a, b⟩
  invFun := fun ⟨⟨current, event⟩, target, a, b⟩ => ⟨current, event, target, a, b⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)

def writeContextEquiv : WriteContext original ≃ WriteContext generated :=
  (writePointContext original).trans ((Equiv.sigmaCongr (pointEquiv p) (fun point =>
    Equiv.sigmaCongr n.support (fun target => Equiv.prodCongr
      ((n.ledger point.2.1).trans
        (Equiv.cast (congrArg (OpenResponsibilityAt G) (p.support_eq point.1 point.2).symm)))
      (n.ledger target)))).trans (writePointContext generated).symm)

def incidenceContextEquiv : IncidenceContext original ≃ IncidenceContext generated :=
  Equiv.prodCongr (pointEquiv p) (Equiv.prodCongr n.incidence n.incidence)

theorem write_incidence_context (context : WriteContext original) :
    incidenceContext (writeContextEquiv p context) = incidenceContextEquiv p (incidenceContext context) := by
  change (pointEquiv p ⟨context.1, context.2.1⟩,
      G.incidenceAt (pointEquiv p ⟨context.1, context.2.1⟩).2.1, G.incidenceAt (n.support context.2.2.1)) =
    (pointEquiv p ⟨context.1, context.2.1⟩, n.incidence (N.incidenceAt context.2.1.1), n.incidence (N.incidenceAt context.2.2.1))
  refine Prod.ext ?_ ?_
  · rfl
  · exact Prod.ext ((congrArg G.incidenceAt (p.support_eq context.1 context.2.1)).trans
      (n.incidence_commutes context.2.1.1)) (n.incidence_commutes context.2.2.1)

def incidenceFamily (old : Transitions original) (context : IncidenceContext generated) : Type :=
  old.Incidence ((incidenceContextEquiv p).symm context)

def exactFamily (old : Transitions original) (context : WriteContext generated) : Type :=
  old.Exact ((writeContextEquiv p).symm context)

def incidenceMemberEquiv (old : Transitions original) (context : IncidenceContext original) :
    old.Incidence context ≃ incidenceFamily p old (incidenceContextEquiv p context) :=
  Equiv.cast (congrArg old.Incidence ((incidenceContextEquiv p).symm_apply_apply context)).symm

def exactMemberEquiv (old : Transitions original) (context : WriteContext original) :
    old.Exact context ≃ exactFamily p old (writeContextEquiv p context) :=
  Equiv.cast (congrArg old.Exact ((writeContextEquiv p).symm_apply_apply context)).symm

def incidenceAtWriteEquiv (old : Transitions original) (context : WriteContext original) :
    old.Incidence (incidenceContext context) ≃ incidenceFamily p old (incidenceContext (writeContextEquiv p context)) :=
  (incidenceMemberEquiv p old (incidenceContext context)).trans
    (Equiv.cast (congrArg (incidenceFamily p old) (write_incidence_context p context).symm))

def transportedProject (old : Transitions original) :
    (context : WriteContext generated) → exactFamily p old context → incidenceFamily p old (incidenceContext context) :=
  Equiv.piCongrLeft _ (writeContextEquiv p) (fun context value =>
    incidenceAtWriteEquiv p old context (old.project context ((exactMemberEquiv p old context).symm value)))

theorem transportedProject_at (old : Transitions original) (context : WriteContext original) :
    transportedProject p old (writeContextEquiv p context) = fun value =>
      incidenceAtWriteEquiv p old context (old.project context ((exactMemberEquiv p old context).symm value)) :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

theorem transportedLineage (old : Transitions original) :
    (context : WriteContext generated) → exactFamily p old context →
      G.lineageAt context.2.1.1 = G.lineageAt context.2.2.1 :=
  Equiv.piCongrLeft _ (writeContextEquiv p) (fun context value =>
    (congrArg G.lineageAt (p.support_eq context.1 context.2.1)).trans
      ((n.lineage_commutes context.2.1.1).trans
        ((congrArg n.lineage (old.lineage context ((exactMemberEquiv p old context).symm value))).trans
          (n.lineage_commutes context.2.2.1).symm)))

/-- Complete fibres are pulled back through the full source presentation.
The dependent project uses the actual incidence-context equality. -/
def transportedTransitions (old : Transitions original) : Transitions generated where
  Incidence := incidenceFamily p old
  Exact := exactFamily p old
  project := transportedProject p old
  lineage := transportedLineage p old

theorem transported_project (old : Transitions original) (context : WriteContext original) (value : old.Exact context) :
    (transportedTransitions p old).project (writeContextEquiv p context) (exactMemberEquiv p old context value) =
      incidenceAtWriteEquiv p old context (old.project context value) := by
  change transportedProject p old _ _ = _
  rw [transportedProject_at]
  exact congrArg (fun x => incidenceAtWriteEquiv p old context (old.project context x))
    ((exactMemberEquiv p old context).symm_apply_apply value)

def transitionTotalEquiv (old : Transitions original) : TransitionTotal old ≃ TransitionTotal (transportedTransitions p old) :=
  Equiv.sumCongr (Equiv.sigmaCongr (incidenceContextEquiv p) (incidenceMemberEquiv p old))
    (Equiv.sigmaCongr (writeContextEquiv p) (exactMemberEquiv p old))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms
