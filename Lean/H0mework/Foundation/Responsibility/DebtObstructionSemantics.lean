import H0mework.Foundation.Responsibility.DebtObstructionBoundary
import H0mework.Foundation.Inquiry.Protocol

/-!
# Root-semantic answer for a direct generated debt obstruction

The maximally faithful root-semantic theory already names every world claim
and realizes it through the world's own holds fibre.  Consequently a direct
debt residual that is already an obstruction of the extended world is an
old-language answer after its same-row U7 audit.  It is not an
expressibility failure and cannot trigger U8.

This audit preserves the live debt row; it neither pays the debt nor creates
an ordinary successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedDebtActivationDirectObstruction
namespace RootSemantic

open DebtActivationWorld
open RootGeneratedDebtActivationDirect
open RootGeneratedDebtActivationU7
open RootInquiryCompletion

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}
variable {source : OccurrenceIndexedSourceAt lower current}
variable (generated : GeneratedObstructionAt source)
variable (oldU7 : U7ProducerCalculus N)
variable (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)

abbrev ExtendedU7 := extendU7 (law := source.law) oldU7

abbrev ExtendedCalculus :=
  extendU7Calculus (law := source.law) oldU7 oldCalculus

/-- The generated domain residual as an obstruction of the already-extended
world, at the exact support carrying the live debt row. -/
def obstruction : source.World.ObstructionAt source.liveLedger.support :=
  debtObstruction (N := N) source.lowerSupport generated.obstruction

def u7Event : (ExtendedCalculus oldU7 oldCalculus).source.EventAt
    (obstruction generated) ((ExtendedU7 oldU7).generateDemand
      (obstruction generated)) :=
  obstructionEvent source oldU7 oldCalculus generated.obstruction

/-- Existing U7 compilation audits the same generated obstruction and the
same live row. -/
def theoryAudit : SourceNativeU7TheoryAuditAt
    (ExtendedCalculus oldU7 oldCalculus)
    (u7Event generated oldU7 oldCalculus) :=
  (generated.sameRowTheoryAudit oldU7 oldCalculus).theoryAudit

/-- Root semantics cannot report an expressibility failure for this already
addressable world obstruction. -/
theorem actualExpressibilityFailure_isEmpty :
    IsEmpty (ActualExpressibilityFailure
      (TheoryState.rootSemantic source.World) (obstruction generated)) :=
  TheoryState.rootSemantic_actualExpressibilityFailure_isEmpty
    source.World (obstruction generated)

/-- Literal old-language expression and lawful realization of the generated
debt obstruction in root semantics. -/
def oldLanguageAnswer : OldLanguageAnswerAt
    (TheoryState.rootSemantic source.World) (obstruction generated) where
  expression := ⟨source.World.obstructionClaim (obstruction generated), rfl⟩
  realization := ULift.up (PLift.up rfl)

/-- The exact inquiry audit is `oldLanguageAnswered`.  U7 has retained the
same row, and root semantics supplies the expression and realization; no U8
failure or revised root is generated. -/
def inquiryAudit : SourceNativeInquiryAuditAt
    (ExtendedU7 oldU7) (ExtendedCalculus oldU7 oldCalculus)
    (TheoryState.rootSemantic source.World) (obstruction generated) :=
  .oldLanguageAnswered (theoryAudit generated oldU7 oldCalculus)
    (oldLanguageAnswer generated)

/-- Source-level view of the same result. -/
def inquiryFrontAudit : SourceNativeInquiryFrontAuditAt
    (ExtendedU7 oldU7) (ExtendedCalculus oldU7 oldCalculus)
    (TheoryState.rootSemantic source.World) source.liveLedger.support :=
  .obstructed (obstruction generated)
    (inquiryAudit generated oldU7 oldCalculus)

end RootSemantic
end RootGeneratedDebtActivationDirectObstruction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
