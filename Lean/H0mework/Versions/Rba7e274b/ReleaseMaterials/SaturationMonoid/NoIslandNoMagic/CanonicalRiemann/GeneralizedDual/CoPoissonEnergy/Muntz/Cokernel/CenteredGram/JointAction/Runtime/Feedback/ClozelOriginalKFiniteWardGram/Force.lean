import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWardGram.Bindings
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWardGram
open Complex MeasureTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace D
export OriginalKFiniteWard.D (factory packet initial firstCfg raw)
end D
namespace L
export OriginalKFiniteWard.L (Value groups)
end L
namespace AI
export OriginalKFiniteWard.AI (withActualInput HasActualInput native_after_admission_input born_after_native_input)
end AI
namespace CF
export OriginalKFiniteWard.CF (collapseValue codeAt code_base_value)
end CF
namespace AS
export OriginalKFiniteWard.AS (AdmissionPacket nativeAfterAdmission bornAfterNative)
end AS
namespace Native
export OriginalKFiniteWard.Native (sourceBorn nativePacket nativeValue selected born_environment)
export ActualCofinalSourceAction (native_packet_actual born_ast packetTransport born_transport)
end Native
namespace R
export OriginalKFiniteWard.R (actualMaterial actionResultAt actionReader)
end R
namespace S
export OriginalKFiniteWard.S (actualOccurrence baseRoot)
end S
local instance sourceGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

-- The same primitive source is arranged as two physical fields before its actual birth.
def transposeBranches : Branches →L[ℂ] Branches :=
  (((ContinuousLinearMap.fst ℂ BurnolL2 BurnolL2).comp
      (ContinuousLinearMap.fst ℂ (BurnolL2 × BurnolL2) (BurnolL2 × BurnolL2))).prod
    ((ContinuousLinearMap.fst ℂ BurnolL2 BurnolL2).comp
      (ContinuousLinearMap.snd ℂ (BurnolL2 × BurnolL2) (BurnolL2 × BurnolL2)))).prod
  (((ContinuousLinearMap.snd ℂ BurnolL2 BurnolL2).comp
      (ContinuousLinearMap.fst ℂ (BurnolL2 × BurnolL2) (BurnolL2 × BurnolL2))).prod
    ((ContinuousLinearMap.snd ℂ BurnolL2 BurnolL2).comp
      (ContinuousLinearMap.snd ℂ (BurnolL2 × BurnolL2) (BurnolL2 × BurnolL2))))

def forceCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .linear (s := ()) (t := ()) transposeBranches.toLinearMap.toAddMonoidHom
    (OriginalKFiniteWard.finiteForceCode observation nontrivial half)

def forceValue : Branches :=
  (((installedOriginalKReceiptAt observation nontrivial half.down).forcing Prior.sourceShift,
    (installedOriginalKReceiptAt observation nontrivial half.down).forcing (-Prior.sourceShift)), 0)

theorem force_code_owned (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    (forceCode observation nontrivial half).eval environment = forceValue observation nontrivial half := by
  change transposeBranches ((OriginalKFiniteWard.finiteForceCode observation nontrivial half).eval environment) = _
  rw [OriginalKFiniteWard.finite_force_code_owned]
  rfl

def forceFactory := AI.withActualInput (forceCode observation nontrivial half) (D.factory observation nontrivial half)
abbrev forceParent (ordinal : Nat) := D.packet observation nontrivial half depth ordinal
abbrev forceIncoming (ordinal : Nat) := AS.nativeAfterAdmission (forceFactory observation nontrivial half)
  (forceParent observation nontrivial half depth ordinal)
def forcePacket (ordinal : Nat) : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()) :=
  AS.bornAfterNative (forceIncoming observation nontrivial half depth ordinal)
abbrev forceBorn (ordinal : Nat) := AS.bornAfterNative
  (AS.nativeAfterAdmission (forceFactory observation nontrivial half)
    (forcePacket observation nontrivial half depth ordinal))

theorem force_born_same_source (ordinal : Nat) :
    forceBorn observation nontrivial half depth ordinal =
      Native.packetTransport (forcePacket observation nontrivial half depth ordinal).2.2.2.down
        (Native.sourceBorn (forceFactory observation nontrivial half)
          (forcePacket observation nontrivial half depth ordinal)) := by
  unfold forceBorn
  rw [Native.native_packet_actual, Native.born_transport]

theorem force_admitted_input (ordinal : Nat) :
    AI.HasActualInput (forceCode observation nontrivial half)
      (forcePacket observation nontrivial half depth ordinal).1
      (forcePacket observation nontrivial half depth ordinal).2.2.1
      (forcePacket observation nontrivial half depth ordinal).2.2.2.down :=
  AI.born_after_native_input _ _ (AI.native_after_admission_input _ (D.factory observation nontrivial half) _)

theorem force_born_input (ordinal : Nat) :
    AI.HasActualInput (forceCode observation nontrivial half)
      (forceBorn observation nontrivial half depth ordinal).1
      (forceBorn observation nontrivial half depth ordinal).2.2.1
      (forceBorn observation nontrivial half depth ordinal).2.2.2.down :=
  AI.born_after_native_input _ _ (AI.native_after_admission_input _ (D.factory observation nontrivial half) _)

theorem force_admitted_value (ordinal : Nat) :
    CF.collapseValue (forcePacket observation nontrivial half depth ordinal).1
      (R.actionResultAt (forcePacket observation nontrivial half depth ordinal).2.1.1
        (forcePacket observation nontrivial half depth ordinal).2.2.1
        (S.actualOccurrence (forcePacket observation nontrivial half depth ordinal).2.1.1)).2.2.1 =
      forceValue observation nontrivial half :=
  (Paid.value_of_actual_input (forceCode observation nontrivial half)
    (forcePacket observation nontrivial half depth ordinal) (force_admitted_input observation nontrivial half depth ordinal)).trans
      (force_code_owned observation nontrivial half _)

attribute [irreducible] forceFactory forcePacket
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWardGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
