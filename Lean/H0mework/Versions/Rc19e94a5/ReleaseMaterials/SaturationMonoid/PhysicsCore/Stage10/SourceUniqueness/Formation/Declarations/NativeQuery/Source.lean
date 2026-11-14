import H0mework.Versions.Rc19e94a5.ReleaseMaterials.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.PhysicalSource.ReceiptCofinal
import H0mework.Versions.Rc19e94a5.Foundation.Inquiry.Protocol
import H0mework.Realization.Faces.ProjectionCoface
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValuePairing

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

noncomputable section

abbrev dynamics := MotherDurationExposure.dynamics
abbrev N := RawGeneratedRoot.network dynamics
abbrev source := MotherDurationExposure.ledgerSource
abbrev Anchor := Sigma MotherPhysicalSource.OccurrenceAt
abbrev Query (law : MotherPhysicalLaws.Law) (anchor : Anchor) :=
  ((MotherPhysicalSource.materialLaw law).historyAt anchor.2).CompletionCarrier
abbrev Key (law : MotherPhysicalLaws.Law) := Sigma (Query law)

def u7 : U7ProducerCalculus N where
  DemandAt := fun obstruction => nomatch obstruction
  generateDemand := fun obstruction => nomatch obstruction

def calculus : U7ObstructionEvolutionCalculus N u7 where
  source :=
    { EventAt := fun obstruction _ => nomatch obstruction
      emit := fun obstruction => nomatch obstruction
      demandGeneratedAt := fun {obstruction} _ => nomatch obstruction
      demandEntryAt := fun {obstruction} _ => nomatch obstruction }
  compile := fun {obstruction} _ => nomatch obstruction

abbrev face (law : MotherPhysicalLaws.Law) (anchor : Anchor) :=
  (MotherPhysicalSource.materialLaw law).faithfulAt anchor.2

def readValue (law : MotherPhysicalLaws.Law) (key : Key law) : Option MotherPhysicalSource.Carrier :=
  match (face law key.1).settleWithResidual with
  | .faithful soundness _ _ => some ((face law key.1).completionEvaluation soundness key.2)
  | .unsound _ _ => none
  | .kernelResidual soundness _ _ => some ((face law key.1).completionEvaluation soundness key.2)
  | .coverageResidual soundness _ _ => some ((face law key.1).completionEvaluation soundness key.2)

abbrev Answer (law : MotherPhysicalLaws.Law) (anchor : Anchor) :=
  Query law anchor × ResidualDispositionOutcome (face law anchor) × Option MotherPhysicalSource.Carrier

def answer (law : MotherPhysicalLaws.Law) (key : Key law) : Answer law key.1 :=
  (key.2, (face law key.1).settleWithResidual, readValue law key)

/-- The anchor includes the complete native event, hence all positive durations stay distinct. -/
def projectionLaw (law : MotherPhysicalLaws.Law) : SourceNativeProjectionLaw source := by
  classical
  exact
    { Projection := Key law × Fin 3
      ActiveAt := fun projection {current} occurrence => PLift (projection.1.1 = ⟨current, occurrence⟩)
      InactiveAt := fun projection {current} occurrence => PLift (projection.1.1 ≠ ⟨current, occurrence⟩)
      classify := fun projection {current} occurrence =>
        if same : projection.1.1 = ⟨current, occurrence⟩ then .inl ⟨same⟩ else .inr ⟨same⟩
      PayloadAt := fun projection {_current} occurrence _ =>
        match projection.2 with
        | 0 => Answer law projection.1.1
        | 1 => SourceNativeInquiryAnswerConsumerTokenAt projection.1.2
            (ULift.up.{1, 0} occurrence) (RawGeneratedRoot.entry dynamics occurrence.1)
            (answer law projection.1)
        | _ => SourceNativeInquiryCompilationTokenAt
            (U7 := u7) (calculus := calculus) (oldTheory := TheoryState.rootSemantic N)
            (RawGeneratedRoot.entry dynamics occurrence.1) projection.1.2
            (ULift.up.{1, 0} occurrence) .answered (Answer law projection.1.1)
      project := fun projection {_current} _occurrence _ => by
        rcases projection with ⟨key, tag⟩
        split
        · exact answer law key
        · exact .canonical
        · exact .canonical (answer law key) }

theorem full_query_retained (law : MotherPhysicalLaws.Law) (key : Key law) :
    (answer law key).1 = key.2 := rfl

theorem other_anchor_inactive (law : MotherPhysicalLaws.Law) (key : Key law) (tag : Fin 3)
    {current : MotherPhysicalSource.Current} (occurrence : MotherPhysicalSource.OccurrenceAt current)
    (different : key.1 ≠ ⟨current, occurrence⟩) :
    (projectionLaw law).classify (key, tag) occurrence = .inr ⟨different⟩ := by
  simp only [projectionLaw, dif_neg different]

def materialSource (law : MotherPhysicalLaws.Law) :
    SourceNativeAuthoritySource N (RawGeneratedRoot.vocabulary dynamics) :=
  (RawGeneratedRoot.authoritySource dynamics).withProjectionCoface
    (MotherPhysicalSource.materialLaw law).toProjectionLaw

def querySource (law : MotherPhysicalLaws.Law) :
    SourceNativeAuthoritySource N (RawGeneratedRoot.vocabulary dynamics) :=
  (materialSource law).withProjectionCoface (projectionLaw law)

def cochainSource (law : MotherPhysicalLaws.Law) :
    SourceNativeAuthoritySource N (RawGeneratedRoot.vocabulary dynamics) :=
  (querySource law).withProjectionCoface
    (RawGeneratedRoot.CofinalAction.cochainComponent
      (MotherPhysicalSource.receiptAction law))

def declarationSource (law : MotherPhysicalLaws.Law) :
    SourceNativeAuthoritySource N (RawGeneratedRoot.vocabulary dynamics) :=
  (cochainSource law).withProjectionCoface
    (RawGeneratedRoot.CofinalAction.valuePairingComponent
      (MotherPhysicalSource.receiptAction law))

def queryInstallation (law : MotherPhysicalLaws.Law) :
    SourceNativeProjectionLaw.InstallationAt (projectionLaw law) (declarationSource law).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (materialSource law) (projectionLaw law)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (querySource law)
      (RawGeneratedRoot.CofinalAction.cochainComponent
        (MotherPhysicalSource.receiptAction law))) |>.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (cochainSource law)
      (RawGeneratedRoot.CofinalAction.valuePairingComponent
        (MotherPhysicalSource.receiptAction law)))

def historyInstallation (law : MotherPhysicalLaws.Law) :
    SourceNativeProjectionLaw.InstallationAt (materialSource law).projectionLaw
      (declarationSource law).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (materialSource law) (projectionLaw law)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (querySource law)
      (RawGeneratedRoot.CofinalAction.cochainComponent
        (MotherPhysicalSource.receiptAction law))) |>.trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (cochainSource law)
      (RawGeneratedRoot.CofinalAction.valuePairingComponent
        (MotherPhysicalSource.receiptAction law)))

def cochainInstallation (law : MotherPhysicalLaws.Law) :
    SourceNativeProjectionLaw.InstallationAt
      (RawGeneratedRoot.CofinalAction.cochainComponent
        (MotherPhysicalSource.receiptAction law))
      (declarationSource law).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface (querySource law)
    (RawGeneratedRoot.CofinalAction.cochainComponent
      (MotherPhysicalSource.receiptAction law))).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (cochainSource law)
      (RawGeneratedRoot.CofinalAction.valuePairingComponent
        (MotherPhysicalSource.receiptAction law)))

def valuePairingInstallation (law : MotherPhysicalLaws.Law) :
    SourceNativeProjectionLaw.InstallationAt
      (RawGeneratedRoot.CofinalAction.valuePairingComponent
        (MotherPhysicalSource.receiptAction law))
      (declarationSource law).projectionLaw :=
  .componentCoface (cochainSource law)
    (RawGeneratedRoot.CofinalAction.valuePairingComponent
      (MotherPhysicalSource.receiptAction law))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery
