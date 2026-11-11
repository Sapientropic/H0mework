import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKContactClosureSourceProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusContactClosureSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKContactClosureSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalKPairedBEulerJunctionSource
namespace A
export OriginalWholeDebtRAdjointContactSource
  (T step positionContact fourierContact contactLift sourceEffect)
end A
namespace S
export OriginalWholeDebtRJointMobiusContactClosureSource
  (closureInput next coefficient actual_input actual_whole_next actual_B_effect)
end S

/-- The reader starts at the complete original B regular source and the two native step carriers. -/
def sourceEnvironment (c : BurnolCompletedMellinCoordinate) : Env Value Var :=
  fun _ => ![BandFullStockEuler.regularSource c,A.step junctionPoint,A.step (1/4)]

theorem source_fields (c : BurnolCompletedMellinCoordinate) :
    sourceEnvironment c () 0 = BandFullStockEuler.regularSource c ∧
      sourceEnvironment c () 1 = A.step junctionPoint ∧
      sourceEnvironment c () 2 = A.step (1/4) := ⟨rfl,rfl,rfl⟩

theorem actual_regular_code (c d : BurnolCompletedMellinCoordinate) :
    (regularCode d).eval (sourceEnvironment c) = A.T d (BandFullStockEuler.regularSource c) := rfl

theorem actual_contact_code (c d : BurnolCompletedMellinCoordinate) (field : Fin 4) :
    (contactCode c d field).eval (sourceEnvironment c) =
      ![sourceJump c 0 • A.positionContact d junctionPoint,
        -(sourceTrace c 0 • A.positionContact d (1/4)),
        -(sourceJump c 1 • A.fourierContact d junctionPoint),
        sourceTrace c 1 • A.fourierContact d (1/4)] field := by
  fin_cases field
  · rfl
  · change (-sourceTrace c 0) • A.positionContact d (1/4) = _
    rw [neg_smul]
    rfl
  · change (-sourceJump c 1) • A.fourierContact d junctionPoint = _
    rw [neg_smul]
    rfl
  · rfl

theorem actual_contacts_code (c d : BurnolCompletedMellinCoordinate) :
    (contactsCode c d).eval (sourceEnvironment c) = A.contactLift c d := by
  change (((contactCode c d 0).eval (sourceEnvironment c) +
    (contactCode c d 1).eval (sourceEnvironment c)) +
    (contactCode c d 2).eval (sourceEnvironment c)) +
    (contactCode c d 3).eval (sourceEnvironment c) = _
  rw [actual_contact_code,actual_contact_code,actual_contact_code,actual_contact_code]
  change ((sourceJump c 0 • A.positionContact d junctionPoint +
    -(sourceTrace c 0 • A.positionContact d (1/4))) +
    -(sourceJump c 1 • A.fourierContact d junctionPoint)) +
    sourceTrace c 1 • A.fourierContact d (1/4) = _
  simp only [OriginalWholeDebtRAdjointContactSource.contactLift,sub_eq_add_neg]

theorem actual_effect_code (c d : BurnolCompletedMellinCoordinate) :
    (effectCode c d).eval (sourceEnvironment c) = A.sourceEffect c d := by
  change (regularCode d).eval (sourceEnvironment c) +
    (contactsCode c d).eval (sourceEnvironment c) = _
  rw [actual_regular_code,actual_contacts_code]
  rfl

theorem actual_input_code (c d : BurnolCompletedMellinCoordinate) :
    (inputCode c d).eval (sourceEnvironment c) = (S.closureInput c d : BurnolL2) := by
  change burnolEvenAmbientProjectionEndomorphism ((effectCode c d).eval (sourceEnvironment c)) = _
  rw [actual_effect_code]
  rfl

theorem actual_code (c d : BurnolCompletedMellinCoordinate) :
    (code c d).eval (sourceEnvironment c) = S.next c d := by
  change burnolDirectRightResolventCLM d ((inputCode c d).eval (sourceEnvironment c)) = _
  rw [actual_input_code]
  rfl

theorem actual_input_physical (c d : BurnolCompletedMellinCoordinate) :
    (inputCode c d).eval (sourceEnvironment c) ∈ evenBurnolClosedFace (1/4) := by
  rw [actual_input_code]
  exact (S.closureInput c d).property

theorem actual_code_source_effect (c d : BurnolCompletedMellinCoordinate) :
    OriginalKCombPhysicalAction.physicalRemainder ((code c d).eval (sourceEnvironment c)) =
      (-2*inner ℂ (fourierL2 (OriginalKSourceResolventReconstruction.generatedK d))
        ((inputCode c d).eval (sourceEnvironment c))) •
        OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.physicalOutsideColumn d := by
  rw [actual_code,actual_input_code]
  exact S.actual_B_effect c d

def sourceReader (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : Half observation) (d : BurnolCompletedMellinCoordinate)
    {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()) :=
  reader (sourceEnvironment (coordinate observation nontrivial half occurrence))
    observation nontrivial half d occurrence

theorem source_reader_source (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : Half observation) (d : BurnolCompletedMellinCoordinate)
    {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (sourceReader observation nontrivial half d occurrence).environment =
      sourceEnvironment (coordinate observation nontrivial half occurrence) ∧
      (sourceReader observation nontrivial half d occurrence).expression =
        code (coordinate observation nontrivial half occurrence) d := ⟨rfl,rfl⟩

end OriginalKContactClosureSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
