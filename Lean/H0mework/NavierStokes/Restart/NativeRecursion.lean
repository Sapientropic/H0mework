import H0mework.NavierStokes.Restart.WholeContinuousMildSerrin

/-!
# Native whole-flow restart recursion

One generated whole receipt now writes its selected positive-time endpoint
as the exact initial state of the next generated whole receipt.  Iterating
this source-owned update produces an infinite typed write-chain with
strictly increasing accumulated physical time.  No continuation oracle,
target state, horizon, cutoff, or branch enters the update.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion

open scoped BigOperators Topology

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open
  ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedCompiler
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalDissipationLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ArithmeticIncidence
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ArithmeticGeneration
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootArithmeticIncidence

noncomputable section

/-- One actual whole-flow current: a generated unforced receipt together
with the positive-time contact it writes. -/
structure GeneratedWholeRestartCurrent (ν : Viscosity) where
  initialState : ComplexVorticityHilbertState
  duration : ℝ
  receipt : WholeContinuousMildSerrinReceipt ν initialState duration
  contact : GeneratedPositiveWholeRestartContact receipt

namespace GeneratedWholeRestartCurrent

/-- Compile the current contact into the next actual whole unforced receipt. -/
noncomputable def nextReceipt
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    WholeContinuousMildSerrinReceipt
      ν current.contact.physicalState
      (wholeRestartDuration current.contact) :=
  generatedWholeRestartWholeContinuousMildSerrinReceipt
    (generatedWholeRestartCanonicalReplay current.contact)

/-- The next receipt generates a late positive endpoint together with the
kinetic payment produced by its exact canonical replay. -/
noncomputable def nextKineticContact
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    GeneratedWholeRestartKineticContact
      (generatedWholeRestartCanonicalReplay current.contact) :=
  generatedWholeRestartKineticContact
    (generatedWholeRestartCanonicalReplay current.contact)

/-- The next receipt itself generates its positive-time endpoint contact;
the authoritative chooser is the kinetic-controlled source producer above. -/
noncomputable abbrev nextContact
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    GeneratedPositiveWholeRestartContact current.nextReceipt :=
  current.nextKineticContact.nextContact

/-- Total source-generated cell effect on the same next-contact occurrence. -/
noncomputable abbrev nextCellEffect
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    GeneratedWholeRestartCellEffectAt current.nextContact :=
  current.nextKineticContact.cellEffect

/-- One native whole update cannot increase complete kinetic-scale mass. -/
theorem nextContact_kineticMass_le
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    puncturedWholeVorticityKineticMass
        current.nextContact.physicalState ≤
      puncturedWholeVorticityKineticMass
        current.contact.physicalState :=
  current.nextKineticContact.kineticMass_le

/-- One native whole update stays below the coefficient-enstrophy ceiling
generated by the exact current from which its receipt was replayed. -/
theorem nextContact_coefficientMass_le
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    wholeVorticityEuclideanMass
        current.nextContact.physicalState ≤
      wholeRestartCoefficientCeiling current.contact :=
  current.nextKineticContact.coefficientMass_le

/-- One native whole update pays its complete unweighted vorticity
dissipation on the same actual positive-time prefix. -/
theorem nextContact_kineticDissipation_le
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    puncturedWholeVorticityKineticMass
          current.nextContact.physicalState +
        2 * ν.coeff *
          wholePrefixVorticityMass current.nextContact.time
            current.nextReceipt.stateLimit ≤
      puncturedWholeVorticityKineticMass
        current.contact.physicalState :=
  current.nextKineticContact.kineticDissipation_le

/-- The actual current decides its own fixed half-critical alternative.  A
crossing is read from the current whole state; otherwise the very same
native endpoint pays the full prefix gradient mass with the sharp factor
transported from the finite enstrophy identity. -/
theorem nextContact_halfCriticalAbsorption_disposition
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 <
        criticalEnstrophyLatticeConstant *
          wholeVorticityEuclideanMass current.contact.physicalState ∨
      wholeVorticityEuclideanMass current.nextContact.physicalState +
          2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
            wholePrefixVorticityGradientMass current.nextContact.time
              current.nextReceipt.stateLimit ≤
        wholeVorticityEuclideanMass current.contact.physicalState :=
  current.nextKineticContact.halfCriticalDisposition

/-- One complete generated edge.  Its target current can only be read through
the same package that carries the emitter's total cell effect. -/
structure GeneratedWholeRestartNextAt
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) : Type where
  private mk ::
  emitted : GeneratedWholeRestartKineticContact
    (generatedWholeRestartCanonicalReplay current.contact)

/-- The total cell effect is a field of the exact contact emitter consumed by
this edge, not an independently reconstructed branch. -/
abbrev GeneratedWholeRestartNextAt.cellEffect
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (generated : GeneratedWholeRestartNextAt current) :
    GeneratedWholeRestartCellEffectAt generated.emitted.nextContact :=
  generated.emitted.cellEffect

abbrev GeneratedWholeRestartNextAt.target
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (generated : GeneratedWholeRestartNextAt current) :
    GeneratedWholeRestartCurrent ν where
  initialState := current.contact.physicalState
  duration := wholeRestartDuration current.contact
  receipt := current.nextReceipt
  contact := generated.emitted.nextContact

@[simp] theorem GeneratedWholeRestartNextAt.target_initialState
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (generated : GeneratedWholeRestartNextAt current) :
    generated.target.initialState = current.contact.physicalState :=
  rfl

@[simp] theorem GeneratedWholeRestartNextAt.target_duration
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (generated : GeneratedWholeRestartNextAt current) :
    generated.target.duration = wholeRestartDuration current.contact :=
  rfl

@[simp] theorem GeneratedWholeRestartNextAt.target_receipt
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (generated : GeneratedWholeRestartNextAt current) :
    generated.target.receipt = current.nextReceipt :=
  rfl

@[simp] theorem GeneratedWholeRestartNextAt.target_contact
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (generated : GeneratedWholeRestartNextAt current) :
    generated.target.contact = generated.emitted.nextContact :=
  rfl

noncomputable abbrev generatedNext
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    GeneratedWholeRestartNextAt current :=
  ⟨current.nextKineticContact⟩

/- These specialized projections preserve the old definitional interface for
downstream whole-run calculations.  They expose no second successor: each
right-hand side is still read from the emitter package above. -/
@[simp] theorem generatedNext_target_initialState
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    current.generatedNext.target.initialState =
      current.contact.physicalState :=
  rfl

@[simp] theorem generatedNext_target_duration
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    current.generatedNext.target.duration =
      wholeRestartDuration current.contact :=
  rfl

@[simp] theorem generatedNext_target_receipt
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    current.generatedNext.target.receipt = current.nextReceipt :=
  rfl

@[simp] theorem generatedNext_target_contact
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    current.generatedNext.target.contact = current.nextContact :=
  rfl

/-- The source-owned native whole update, projected from the complete edge
package rather than reconstructed from a contact-only sequence. -/
noncomputable def next
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    GeneratedWholeRestartCurrent ν :=
  current.generatedNext.target

@[simp] theorem next_initialState
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    current.next.initialState = current.contact.physicalState := rfl

@[simp] theorem next_duration
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    current.next.duration = wholeRestartDuration current.contact := rfl

@[simp] theorem next_contact
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    current.next.contact = current.nextContact := rfl

/-- The next actual receipt begins at the exact endpoint written by the
current contact. -/
theorem nextReceipt_initial
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    current.nextReceipt.wholePath
        ⟨0, ⟨le_rfl, current.nextReceipt.requestedTimePos.le⟩⟩ =
      current.contact.physicalState :=
  current.nextReceipt.wholePath_initial

/-- The next selected state is literally the terminal state of its actual
positive-time unforced prefix. -/
theorem nextContact_prefix_terminal
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    (current.nextContact.prefixReceipt.wholePath
        ⟨current.nextContact.time.1,
          ⟨current.nextContact.time_pos.le, le_rfl⟩⟩) =
      current.nextContact.physicalState :=
  current.nextContact.prefixReceipt_terminal

/-- Finite source-generated physical path.  It records only actual `.next`
edges and therefore cannot contain a completed future table. -/
inductive GeneratedWholeRestartCurrentPathAt
    {ν : Viscosity}
    (source : GeneratedWholeRestartCurrent ν) :
    GeneratedWholeRestartCurrent ν → Type
  | refl : GeneratedWholeRestartCurrentPathAt source source
  | next {target : GeneratedWholeRestartCurrent ν} :
      GeneratedWholeRestartCurrentPathAt source target →
        GeneratedWholeRestartCurrentPathAt source target.next

/-- One unresolved cell debt transported to an exact generated current.
The residual occurrence is fixed at `origin`; `path` proves that every later
standing is reached only by the physical `.next` compiler. -/
structure GeneratedWholeRestartPendingCellAt
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) : Type where
  private mk ::
  origin : GeneratedWholeRestartCurrent ν
  residual : GeneratedWholeRestartRetainedCellResidualAt origin.nextContact
  path : GeneratedWholeRestartCurrentPathAt origin.next current
  cellDeficit : ℝ
  cellDeficit_eq :
    cellDeficit =
      (wholeRestartCoefficientLevel origin.contact : ℝ) - 1 -
        wholeVorticityEuclideanMass current.contact.physicalState
  cellDeficit_nonneg : 0 ≤ cellDeficit

private def generatedWholeRestartPendingCellOfResidual
    {ν : Viscosity}
    (source : GeneratedWholeRestartCurrent ν)
    (residual : GeneratedWholeRestartRetainedCellResidualAt
      source.nextContact) :
    GeneratedWholeRestartPendingCellAt source.next where
  origin := source
  residual := residual
  path := .refl
  cellDeficit := residual.cellDeficit
  cellDeficit_eq := by
    change residual.cellDeficit =
      (wholeRestartCoefficientLevel source.contact : ℝ) - 1 -
        wholeVorticityEuclideanMass source.nextContact.physicalState
    exact residual.cellDeficit_eq
  cellDeficit_nonneg := residual.cellDeficit_nonneg

/-- A strictly positive but not-yet-settling action transports the unique
residual and subtracts that action's exact physical debit.  Positivity is
checked by the standing compiler before this private constructor is used. -/
private def carryGeneratedWholeRestartPendingCell
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current)
    (notPaid : ¬ pending.cellDeficit <
      current.nextCellEffect.debit.netEnstrophyDebit) :
    GeneratedWholeRestartPendingCellAt current.next where
  origin := pending.origin
  residual := pending.residual
  path := .next pending.path
  cellDeficit :=
    pending.cellDeficit - current.nextCellEffect.debit.netEnstrophyDebit
  cellDeficit_eq := by
    rw [pending.cellDeficit_eq,
      current.nextCellEffect.debit.netEnstrophyDebit_eq,
      current.nextCellEffect.debit.sourcePhysicalState_eq,
      current.nextCellEffect.debit.targetPhysicalState_eq]
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    rw [next_contact]
    ring_nf
    rfl
  cellDeficit_nonneg :=
    sub_nonneg.mpr (le_of_not_gt notPaid)

namespace GeneratedWholeRestartPendingCellAt

/-- A live debt keeps the current physical state below the exact cell wall
of its unique origin. -/
theorem currentMass_le_originCellWall
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current) :
    wholeVorticityEuclideanMass current.contact.physicalState ≤
      (wholeRestartCoefficientLevel pending.origin.contact : ℝ) - 1 := by
  have deficitNonneg := pending.cellDeficit_nonneg
  rw [pending.cellDeficit_eq] at deficitNonneg
  linarith

/-- Consequently, transporting one debt can never masquerade as a new scale
above its origin. -/
theorem currentLevel_le_originLevel
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current) :
    wholeRestartCoefficientLevel current.contact ≤
      wholeRestartCoefficientLevel pending.origin.contact := by
  apply Nat.ceil_le.mpr
  rw [wholeRestartRawCoefficientCeiling_eq]
  simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
  linarith [pending.currentMass_le_originCellWall]

end GeneratedWholeRestartPendingCellAt

/-- Valued arithmetic material of the unique live debt: the current action's
physical debit is evaluated against the origin and target cell histories. -/
def GeneratedWholeRestartPendingCellArithmeticMaterialAt
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current) :
    RootArithmeticMaterialAt where
  whole := WholeRestartContactCellHistoryAt current.nextContact
  left := WholeRestartContactCellHistoryAt pending.origin.contact
  right := WholeRestartContactOnePaidCellHistory

/-- Macro one-cell exact normal form generated when the current action
settles the debt retained from its exact origin occurrence. -/
def GeneratedWholeRestartPendingCellIncidenceAt
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current) : Prop :=
  let material := GeneratedWholeRestartPendingCellArithmeticMaterialAt pending
  material.whole = material.left.parallel material.right

/-- Paying the live remaining deficit forces an exact one-cell cardinal
update from the retained origin. -/
theorem pendingCellLevel_eq_add_one_of_paid
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current)
    (paid : pending.cellDeficit <
      current.nextCellEffect.debit.netEnstrophyDebit) :
    wholeRestartCoefficientLevel current.nextContact =
      wholeRestartCoefficientLevel pending.origin.contact + 1 := by
  have currentLevel_le_originLevel :
      wholeRestartCoefficientLevel current.contact ≤
        wholeRestartCoefficientLevel pending.origin.contact :=
    pending.currentLevel_le_originLevel
  have targetMass_le_currentLevel := current.nextContact_coefficientMass_le
  have currentLevelCast_le_originLevel :
      (wholeRestartCoefficientLevel current.contact : ℝ) ≤
        wholeRestartCoefficientLevel pending.origin.contact := by
    exact_mod_cast currentLevel_le_originLevel
  have targetMass_le_originLevel :
      wholeVorticityEuclideanMass current.nextContact.physicalState ≤
        (wholeRestartCoefficientLevel pending.origin.contact : ℝ) := by
    change
      wholeVorticityEuclideanMass current.nextContact.physicalState ≤
        (wholeRestartCoefficientLevel current.contact : ℝ) at targetMass_le_currentLevel
    exact targetMass_le_currentLevel.trans currentLevelCast_le_originLevel
  have targetRaw_le_originSucc :
      wholeRestartRawCoefficientCeiling current.nextContact ≤
        ((wholeRestartCoefficientLevel pending.origin.contact + 1 : ℕ) : ℝ) := by
    rw [wholeRestartRawCoefficientCeiling_eq]
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact,
      Nat.cast_add, Nat.cast_one]
    linarith
  have targetLevel_le_originSucc :
      wholeRestartCoefficientLevel current.nextContact ≤
        wholeRestartCoefficientLevel pending.origin.contact + 1 :=
    Nat.ceil_le.mpr targetRaw_le_originSucc
  have originWall_lt_targetMass :
      (wholeRestartCoefficientLevel pending.origin.contact : ℝ) - 1 <
        wholeVorticityEuclideanMass current.nextContact.physicalState := by
    rw [pending.cellDeficit_eq,
      current.nextCellEffect.debit.netEnstrophyDebit_eq,
      current.nextCellEffect.debit.sourcePhysicalState_eq,
      current.nextCellEffect.debit.targetPhysicalState_eq] at paid
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
      at paid
    exact (sub_lt_sub_iff_right
      (wholeVorticityEuclideanMass current.contact.physicalState)).mp paid
  have originLevel_lt_targetRaw :
      (wholeRestartCoefficientLevel pending.origin.contact : ℝ) <
        wholeRestartRawCoefficientCeiling current.nextContact := by
    rw [wholeRestartRawCoefficientCeiling_eq]
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    linarith
  have originLevel_lt_targetLevel :
      wholeRestartCoefficientLevel pending.origin.contact <
        wholeRestartCoefficientLevel current.nextContact :=
    (Nat.lt_ceil).2 originLevel_lt_targetRaw
  omega

/-- If the very next action settles a retained debt, the intermediate
current cannot have fallen below the origin cell.  Otherwise the ordinary
one-edge no-upward-skip bound could not reach `origin + 1` in that action. -/
theorem pendingCell_currentLevel_eq_originLevel_of_paid
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current)
    (paid : pending.cellDeficit <
      current.nextCellEffect.debit.netEnstrophyDebit) :
    wholeRestartCoefficientLevel current.contact =
      wholeRestartCoefficientLevel pending.origin.contact := by
  have targetLevelEq := pendingCellLevel_eq_add_one_of_paid pending paid
  have targetMassLe := current.nextContact_coefficientMass_le
  have targetRawLeCurrentSucc :
      wholeRestartRawCoefficientCeiling current.nextContact ≤
        ((wholeRestartCoefficientLevel current.contact + 1 : Nat) : Real) := by
    rw [wholeRestartRawCoefficientCeiling_eq]
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact,
      Nat.cast_add, Nat.cast_one]
    change
      wholeVorticityEuclideanMass current.nextContact.physicalState + 1 ≤
        (wholeRestartCoefficientLevel current.contact : Real) + 1
    change
      wholeVorticityEuclideanMass current.nextContact.physicalState ≤
        (wholeRestartCoefficientLevel current.contact : Real) at targetMassLe
    linarith
  have targetLevelLeCurrentSucc :
      wholeRestartCoefficientLevel current.nextContact ≤
        wholeRestartCoefficientLevel current.contact + 1 :=
    Nat.ceil_le.mpr targetRawLeCurrentSucc
  have currentLevelLeOrigin := pending.currentLevel_le_originLevel
  omega

/-- Exact settlement of one retained debt by the current action. -/
structure GeneratedWholeRestartPendingCellSettlementAt
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current) : Type where
  private mk ::
  paid : pending.cellDeficit <
    current.nextCellEffect.debit.netEnstrophyDebit
  incidence : GeneratedWholeRestartPendingCellIncidenceAt pending

private def generatedWholeRestartPendingCellSettlementOfPaid
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current)
    (paid : pending.cellDeficit <
      current.nextCellEffect.debit.netEnstrophyDebit) :
    GeneratedWholeRestartPendingCellSettlementAt pending where
  paid := paid
  incidence := by
    let levelEq := pendingCellLevel_eq_add_one_of_paid pending paid
    apply UnitHistory.eq_of_cardinalShadow_eq
    simpa only [GeneratedWholeRestartPendingCellArithmeticMaterialAt,
      UnitHistory.cardinalShadow_parallel,
      WholeRestartContactCellHistoryAt_cardinalShadow,
      WholeRestartContactOnePaidCellHistory_cardinalShadow] using levelEq

/-- Total same-debt disposition generated by the next actual action.  The
retained branch transports the old debt; it cannot contain a new residual. -/
inductive GeneratedWholeRestartPendingCellDispositionAt
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current) : Type
  | settled
      (settlement : GeneratedWholeRestartPendingCellSettlementAt pending)
  | retained
      (notPaid : ¬ pending.cellDeficit <
        current.nextCellEffect.debit.netEnstrophyDebit)

noncomputable def generatedWholeRestartPendingCellDisposition
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current) :
    GeneratedWholeRestartPendingCellDispositionAt pending := by
  by_cases paid : pending.cellDeficit <
      current.nextCellEffect.debit.netEnstrophyDebit
  · exact .settled
      (generatedWholeRestartPendingCellSettlementOfPaid pending paid)
  · exact .retained paid

def GeneratedWholeRestartPendingCellDispositionAt.IsSettled
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {pending : GeneratedWholeRestartPendingCellAt current} :
    GeneratedWholeRestartPendingCellDispositionAt pending → Prop
  | .settled _settlement => True
  | .retained _notPaid => False

/-- Settlement is exactly the strict physical debit test used by the source
compiler; the branch carries no independent selector. -/
theorem generatedPendingCellDisposition_isSettled_iff_paid
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current) :
    (generatedWholeRestartPendingCellDisposition pending).IsSettled ↔
      pending.cellDeficit <
        current.nextCellEffect.debit.netEnstrophyDebit := by
  by_cases paid : pending.cellDeficit <
      current.nextCellEffect.debit.netEnstrophyDebit
  · rw [show generatedWholeRestartPendingCellDisposition pending =
        .settled
          (generatedWholeRestartPendingCellSettlementOfPaid pending paid) by
      simp [generatedWholeRestartPendingCellDisposition, paid]]
    change True ↔ _
    simp [paid]
  · rw [show generatedWholeRestartPendingCellDisposition pending =
        .retained paid by
      simp [generatedWholeRestartPendingCellDisposition, paid]]
    change False ↔ _
    simp [paid]

/-- Exact physical readout of retained-cell settlement.  After one residual,
the immediately following action settles that same debt exactly when its
actual endpoint crosses the original occurrence's cell wall. -/
theorem generatedPendingCellDisposition_isSettled_iff_originCellWall_lt_targetMass
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current) :
    (generatedWholeRestartPendingCellDisposition pending).IsSettled ↔
      (wholeRestartCoefficientLevel pending.origin.contact : ℝ) - 1 <
        wholeVorticityEuclideanMass current.nextContact.physicalState := by
  rw [generatedPendingCellDisposition_isSettled_iff_paid,
    pending.cellDeficit_eq,
    current.nextCellEffect.debit.netEnstrophyDebit_eq,
    current.nextCellEffect.debit.sourcePhysicalState_eq,
    current.nextCellEffect.debit.targetPhysicalState_eq]
  simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
  exact sub_lt_sub_iff_right
    (wholeVorticityEuclideanMass current.contact.physicalState)

/-- Complete live cell standing at one physical current.

A nonpositive settlement action does not create an absorbing historical
failure state.  The unique debt remains the current row and is revalued by
the next actual source action.  The obstruction is exposed by the total
effect emitted on that edge, not frozen into a second transition system. -/
inductive GeneratedWholeRestartCellStandingAt
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) : Type
  | clear
  | pending (debt : GeneratedWholeRestartPendingCellAt current)

/-- Remaining real-valued distance to the unique cell wall represented by
the current standing.  A clear standing reads the current cell gap; a pending
standing keeps the exact origin-indexed deficit already transported by the
source compiler. -/
def GeneratedWholeRestartCellStandingAt.remainingCellDeficit
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν} :
    GeneratedWholeRestartCellStandingAt current → ℝ
  | .clear =>
      (wholeRestartCoefficientLevel current.contact : ℝ) - 1 -
        wholeVorticityEuclideanMass current.contact.physicalState
  | .pending debt => debt.cellDeficit

theorem GeneratedWholeRestartCellStandingAt.remainingCellDeficit_nonneg
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (standing : GeneratedWholeRestartCellStandingAt current) :
    0 ≤ standing.remainingCellDeficit := by
  cases standing with
  | clear =>
      have rawLe := wholeRestartRawCoefficientCeiling_le current.contact
      rw [wholeRestartRawCoefficientCeiling_eq] at rawLe
      simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
        at rawLe
      change
        wholeVorticityEuclideanMass current.contact.physicalState + 1 ≤
          (wholeRestartCoefficientLevel current.contact : ℝ) at rawLe
      simpa only [GeneratedWholeRestartCellStandingAt.remainingCellDeficit]
        using sub_nonneg.mpr (by linarith :
          wholeVorticityEuclideanMass current.contact.physicalState ≤
            (wholeRestartCoefficientLevel current.contact : ℝ) - 1)
  | pending debt =>
      exact debt.cellDeficit_nonneg

/-- The standing update consumes the exact current emitter.  A clear row may
admit one fresh residual.  Every later action revalues that same row: a paid
action closes it, while an unpaid action transports its exact remaining
deficit to the compiler-generated successor. -/
noncomputable def GeneratedWholeRestartCellStandingAt.next
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν} :
    GeneratedWholeRestartCellStandingAt current →
      GeneratedWholeRestartCellStandingAt current.next
  | .clear =>
      match current.nextCellEffect with
      | .oneCell _debit _incidence => .clear
      | .retainedResidual residual =>
          .pending
            (generatedWholeRestartPendingCellOfResidual current residual)
  | .pending debt =>
      match generatedWholeRestartPendingCellDisposition debt with
      | .settled _settlement => .clear
      | .retained notPaid =>
          .pending (carryGeneratedWholeRestartPendingCell debt notPaid)

/-- Once a residual is live, the next action either settles it, strictly
reduces the same deficit, or exposes a nonpositive valued obstruction while
retaining that exact row for the next actual action. -/
theorem pendingStanding_next_clear_or_paidSameDebt_or_nonpositiveObstruction
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (debt : GeneratedWholeRestartPendingCellAt current) :
    (GeneratedWholeRestartCellStandingAt.pending debt).next = .clear ∨
      (∃ nextDebt : GeneratedWholeRestartPendingCellAt current.next,
        (GeneratedWholeRestartCellStandingAt.pending debt).next =
            .pending nextDebt ∧
          nextDebt.origin = debt.origin ∧
          HEq nextDebt.residual debt.residual ∧
          0 < current.nextCellEffect.debit.netEnstrophyDebit ∧
          nextDebt.cellDeficit = debt.cellDeficit -
            current.nextCellEffect.debit.netEnstrophyDebit) ∨
      ∃ nextDebt : GeneratedWholeRestartPendingCellAt current.next,
        (GeneratedWholeRestartCellStandingAt.pending debt).next =
            .pending nextDebt ∧
          nextDebt.origin = debt.origin ∧
          HEq nextDebt.residual debt.residual ∧
          ¬ 0 < current.nextCellEffect.debit.netEnstrophyDebit ∧
          nextDebt.cellDeficit = debt.cellDeficit -
            current.nextCellEffect.debit.netEnstrophyDebit := by
  generalize dispositionEq :
      generatedWholeRestartPendingCellDisposition debt = disposition
  cases disposition with
  | settled settlement =>
      exact Or.inl (by simp [GeneratedWholeRestartCellStandingAt.next,
        dispositionEq])
  | retained notPaid =>
      by_cases debitPos : 0 <
          current.nextCellEffect.debit.netEnstrophyDebit
      · refine Or.inr <| Or.inl
          ⟨carryGeneratedWholeRestartPendingCell debt notPaid,
            ?_, rfl, ?_, debitPos, rfl⟩
        · simp [GeneratedWholeRestartCellStandingAt.next, dispositionEq]
        · rfl
      · refine Or.inr <| Or.inr
          ⟨carryGeneratedWholeRestartPendingCell debt notPaid,
            ?_, rfl, ?_, debitPos, rfl⟩
        · simp [GeneratedWholeRestartCellStandingAt.next, dispositionEq]
        · rfl

/-- A strictly positive same-edge debit rules out persistent failure.  It
either closes the origin cell or advances the unique residual with a smaller
deficit. -/
theorem pendingStanding_next_clear_or_paidSameDebt_of_debit_pos
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (debt : GeneratedWholeRestartPendingCellAt current)
    (debitPos : 0 < current.nextCellEffect.debit.netEnstrophyDebit) :
    (GeneratedWholeRestartCellStandingAt.pending debt).next = .clear ∨
      ∃ nextDebt : GeneratedWholeRestartPendingCellAt current.next,
        (GeneratedWholeRestartCellStandingAt.pending debt).next =
            .pending nextDebt ∧
          nextDebt.origin = debt.origin ∧
          HEq nextDebt.residual debt.residual ∧
          nextDebt.cellDeficit < debt.cellDeficit := by
  rcases pendingStanding_next_clear_or_paidSameDebt_or_nonpositiveObstruction
      debt with settled | paid | failed
  · exact Or.inl settled
  · rcases paid with
      ⟨nextDebt, nextEq, originEq, residualEq, _edgePos, deficitEq⟩
    refine Or.inr ⟨nextDebt, nextEq, originEq, residualEq, ?_⟩
    rw [deficitEq]
    exact sub_lt_self debt.cellDeficit debitPos
  · rcases failed with
      ⟨_nextDebt, _nextEq, _originEq, _residualEq, notPositive, _deficitEq⟩
    exact (notPositive debitPos).elim

private theorem valuedOneCell_level_eq_add_one
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (debit : GeneratedWholeRestartCellDebitAt
      (generatedWholeRestartCanonicalReplay current.contact)
      current.nextContact)
    (exact : debit.ExactValuedOneCellAt) :
    wholeRestartCoefficientLevel current.nextContact =
      wholeRestartCoefficientLevel current.contact + 1 := by
  exact debit.coefficientLevel_eq_add_one_of_exact exact

/-- A retained debt is settled by the next actual edge exactly when the
current has recovered the retained origin level and that edge's own emitter
returns the source-generated one-cell incidence.  In particular, a second
raw residual cannot be reinterpreted as settlement merely through its
numerical debit. -/
theorem pendingDisposition_isSettled_iff_originLevel_and_oneCell
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current) :
    (generatedWholeRestartPendingCellDisposition pending).IsSettled ↔
      wholeRestartCoefficientLevel current.contact =
          wholeRestartCoefficientLevel pending.origin.contact ∧
        ∃ (debit : GeneratedWholeRestartCellDebitAt
              (generatedWholeRestartCanonicalReplay current.contact)
              current.nextContact)
            (exact : debit.ExactValuedOneCellAt),
          current.nextCellEffect = .oneCell debit exact := by
  constructor
  · intro settled
    have paid :=
      (generatedPendingCellDisposition_isSettled_iff_paid pending).1 settled
    have currentLevelEq :=
      pendingCell_currentLevel_eq_originLevel_of_paid pending paid
    have targetLevelEq := pendingCellLevel_eq_add_one_of_paid pending paid
    have currentTargetLevelEq :
        wholeRestartCoefficientLevel current.nextContact =
          wholeRestartCoefficientLevel current.contact + 1 :=
      targetLevelEq.trans
        (congrArg (fun level : Nat => level + 1) currentLevelEq.symm)
    generalize effectEq : current.nextCellEffect = effect
    cases effect with
    | oneCell debit exact =>
        exact ⟨currentLevelEq, debit, exact, rfl⟩
    | retainedResidual residual =>
        have exact := residual.debit.exact_of_coefficientLevel_eq_add_one
          currentTargetLevelEq
        exact (residual.normalResidual.mismatch exact).elim
  · rintro ⟨currentLevelEq, debit, exact, effectEq⟩
    apply (generatedPendingCellDisposition_isSettled_iff_paid pending).2
    have targetLevelEq := valuedOneCell_level_eq_add_one debit exact
    have currentLevelLtTargetLevel :
        wholeRestartCoefficientLevel current.contact <
          wholeRestartCoefficientLevel current.nextContact := by
      rw [targetLevelEq]
      omega
    have currentLevelLtTargetRaw :
        (wholeRestartCoefficientLevel current.contact : ℝ) <
          wholeRestartRawCoefficientCeiling current.nextContact :=
      (Nat.lt_ceil).1 currentLevelLtTargetLevel
    have targetMassCrossesCurrentWall :
        (wholeRestartCoefficientLevel current.contact : ℝ) - 1 <
          wholeVorticityEuclideanMass current.nextContact.physicalState := by
      rw [wholeRestartRawCoefficientCeiling_eq] at currentLevelLtTargetRaw
      simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
        at currentLevelLtTargetRaw
      linarith
    rw [pending.cellDeficit_eq, effectEq]
    simp only [GeneratedWholeRestartCellEffectAt.debit]
    rw [debit.netEnstrophyDebit_eq, debit.sourcePhysicalState_eq,
      debit.targetPhysicalState_eq]
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    rw [← currentLevelEq]
    exact (sub_lt_sub_iff_right
      (wholeVorticityEuclideanMass current.contact.physicalState)).2
        targetMassCrossesCurrentWall

/-- Two consecutive raw residual emissions cannot close the first debt.  The
second occurrence is never a hidden one-cell payment; the standing compiler
subsequently classifies its exact debit as paid same-debt carry or persistent
failure. -/
theorem pendingDisposition_notSettled_of_retainedResidual
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (pending : GeneratedWholeRestartPendingCellAt current)
    (residual : GeneratedWholeRestartRetainedCellResidualAt
      current.nextContact)
    (effectEq : current.nextCellEffect = .retainedResidual residual) :
    ¬ (generatedWholeRestartPendingCellDisposition pending).IsSettled := by
  intro settled
  obtain ⟨_currentLevelEq, debit, incidence, oneCellEq⟩ :=
    (pendingDisposition_isSettled_iff_originLevel_and_oneCell pending).1
      settled
  rw [effectEq] at oneCellEq
  cases oneCellEq

/-- Level whose next unit payment is being tracked by a standing.  A clear
standing is anchored at the current contact; a pending standing remains
anchored at the exact occurrence which emitted its unique residual. -/
def GeneratedWholeRestartCellStandingAt.anchorLevel
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν} :
    GeneratedWholeRestartCellStandingAt current → Nat
  | .clear => wholeRestartCoefficientLevel current.contact
  | .pending debt => wholeRestartCoefficientLevel debt.origin.contact

theorem GeneratedWholeRestartCellStandingAt.remainingCellDeficit_eq_anchorLevel_sub_physicalMass
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (standing : GeneratedWholeRestartCellStandingAt current) :
    standing.remainingCellDeficit =
      (standing.anchorLevel : Real) - 1 -
        wholeVorticityEuclideanMass current.contact.physicalState := by
  cases standing with
  | clear => rfl
  | pending debt => exact debt.cellDeficit_eq

/-- Unit payment generated by one standing transition.  Admission of a
residual or transport of persistent failure is not a payment; direct
incidence and settlement of the unique live debt each contribute one. -/
noncomputable def GeneratedWholeRestartCellStandingAt.paymentIncrement
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν} :
    GeneratedWholeRestartCellStandingAt current → Nat
  | .clear =>
      match current.nextCellEffect with
      | .oneCell _debit _incidence => 1
      | .retainedResidual _residual => 0
  | .pending debt =>
      match generatedWholeRestartPendingCellDisposition debt with
      | .settled _settlement => 1
      | .retained _notPaid => 0

/-- Local source obligation carried by one standing: a clear standing has no
live debt, a pending standing must be settled by its current action, and a
persistent failure cannot inhabit an immediately settled active lineage. -/
noncomputable def GeneratedWholeRestartCellStandingAt.IsImmediatelySettled
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν} :
    GeneratedWholeRestartCellStandingAt current → Prop
  | .clear => True
  | .pending debt =>
      (generatedWholeRestartPendingCellDisposition debt).IsSettled

/-- Under the local settlement obligation, the current level itself equals
the standing anchor; a paid residual cannot hide an intermediate scale drop. -/
theorem cellStanding_currentLevel_eq_anchorLevel_of_immediatelySettled
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (standing : GeneratedWholeRestartCellStandingAt current)
    (settled : standing.IsImmediatelySettled) :
    wholeRestartCoefficientLevel current.contact = standing.anchorLevel := by
  cases standing with
  | clear => rfl
  | pending debt =>
      exact pendingCell_currentLevel_eq_originLevel_of_paid debt
        ((generatedPendingCellDisposition_isSettled_iff_paid debt).1 settled)

/-- Across any two consecutive standing transitions, immediate settlement
of the live debt forces at least one actual unit payment. -/
theorem cellStanding_twoStepPayment
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (standing : GeneratedWholeRestartCellStandingAt current)
    (settled : standing.IsImmediatelySettled)
    (nextSettled : standing.next.IsImmediatelySettled) :
    1 ≤ standing.paymentIncrement + standing.next.paymentIncrement := by
  cases standing with
  | clear =>
      generalize effectEq : current.nextCellEffect = effect
      cases effect with
      | oneCell debit incidence =>
          simp [GeneratedWholeRestartCellStandingAt.paymentIncrement,
            GeneratedWholeRestartCellStandingAt.next, effectEq]
      | retainedResidual residual =>
          simp only [GeneratedWholeRestartCellStandingAt.paymentIncrement,
            GeneratedWholeRestartCellStandingAt.next, effectEq,
            Nat.zero_add]
          have residualSettled :
              (generatedWholeRestartPendingCellDisposition
                (generatedWholeRestartPendingCellOfResidual current residual)
                ).IsSettled := by
            simpa [GeneratedWholeRestartCellStandingAt.IsImmediatelySettled,
              GeneratedWholeRestartCellStandingAt.next, effectEq] using
                nextSettled
          generalize dispositionEq :
            generatedWholeRestartPendingCellDisposition
                (generatedWholeRestartPendingCellOfResidual current residual) =
              disposition
          cases disposition with
          | settled settlement => simp
          | retained notPaid =>
              simp [GeneratedWholeRestartPendingCellDispositionAt.IsSettled,
                dispositionEq] at residualSettled
  | pending debt =>
      change
        (generatedWholeRestartPendingCellDisposition debt).IsSettled at settled
      generalize dispositionEq :
        generatedWholeRestartPendingCellDisposition debt = disposition
      cases disposition with
      | settled settlement =>
          simp [GeneratedWholeRestartCellStandingAt.paymentIncrement,
            dispositionEq]
      | retained notPaid =>
          simp [GeneratedWholeRestartPendingCellDispositionAt.IsSettled,
            dispositionEq] at settled

/-- One exact standing transition commutes with its unit-payment readout. -/
theorem cellStanding_anchorLevel_next
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (standing : GeneratedWholeRestartCellStandingAt current) :
    standing.next.anchorLevel =
      standing.anchorLevel + standing.paymentIncrement := by
  cases standing with
  | clear =>
      generalize effectEq : current.nextCellEffect = effect
      cases effect with
      | oneCell debit incidence =>
          simp only [GeneratedWholeRestartCellStandingAt.next,
            GeneratedWholeRestartCellStandingAt.anchorLevel,
            GeneratedWholeRestartCellStandingAt.paymentIncrement,
            effectEq, Nat.add_one]
          rw [next_contact]
          convert valuedOneCell_level_eq_add_one debit incidence using 1
          rfl
      | retainedResidual residual =>
          simp [GeneratedWholeRestartCellStandingAt.next,
            GeneratedWholeRestartCellStandingAt.anchorLevel,
            GeneratedWholeRestartCellStandingAt.paymentIncrement,
            effectEq, generatedWholeRestartPendingCellOfResidual]
  | pending debt =>
      generalize dispositionEq :
        generatedWholeRestartPendingCellDisposition debt = disposition
      cases disposition with
      | settled settlement =>
          simp only [GeneratedWholeRestartCellStandingAt.next,
            GeneratedWholeRestartCellStandingAt.anchorLevel,
            GeneratedWholeRestartCellStandingAt.paymentIncrement,
            dispositionEq, Nat.add_one]
          rw [next_contact]
          convert pendingCellLevel_eq_add_one_of_paid debt settlement.paid using 1
          rfl
      | retained notPaid =>
          simp [GeneratedWholeRestartCellStandingAt.next,
            GeneratedWholeRestartCellStandingAt.anchorLevel,
            GeneratedWholeRestartCellStandingAt.paymentIncrement,
            dispositionEq, carryGeneratedWholeRestartPendingCell]

/-! ## Standing-aware total emitter -/

/-- Total cell effect emitted from the complete current standing.  A raw
failed-incidence receipt can open a residual only from `.clear`.  Once that
debt is live, the next actual action is typed as settlement, strict partial
payment, or persistent failure; it cannot be presented as a second residual
opening. -/
inductive GeneratedWholeRestartStandingCellEffectAt
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν} :
    GeneratedWholeRestartCellStandingAt current → Type
  | directOneCell
      (debit : GeneratedWholeRestartCellDebitAt
        (generatedWholeRestartCanonicalReplay current.contact)
        current.nextContact)
      (exact : debit.ExactValuedOneCellAt)
      (effectEq : current.nextCellEffect = .oneCell debit exact) :
      GeneratedWholeRestartStandingCellEffectAt .clear
  | opensResidual
      (residual : GeneratedWholeRestartRetainedCellResidualAt
        current.nextContact)
      (effectEq : current.nextCellEffect = .retainedResidual residual) :
      GeneratedWholeRestartStandingCellEffectAt .clear
  | settlesPending
      (debt : GeneratedWholeRestartPendingCellAt current)
      (settlement : GeneratedWholeRestartPendingCellSettlementAt debt)
      (dispositionEq :
        generatedWholeRestartPendingCellDisposition debt =
          .settled settlement) :
      GeneratedWholeRestartStandingCellEffectAt (.pending debt)
  | strictPartialPayment
      (debt : GeneratedWholeRestartPendingCellAt current)
      (notPaid : ¬ debt.cellDeficit <
        current.nextCellEffect.debit.netEnstrophyDebit)
      (debitPos : 0 < current.nextCellEffect.debit.netEnstrophyDebit)
      (dispositionEq :
        generatedWholeRestartPendingCellDisposition debt =
          .retained notPaid) :
      GeneratedWholeRestartStandingCellEffectAt (.pending debt)
  | persistentFailure
      (debt : GeneratedWholeRestartPendingCellAt current)
      (notPaid : ¬ debt.cellDeficit <
        current.nextCellEffect.debit.netEnstrophyDebit)
      (notPositive : ¬ 0 <
        current.nextCellEffect.debit.netEnstrophyDebit)
      (dispositionEq :
        generatedWholeRestartPendingCellDisposition debt =
          .retained notPaid) :
      GeneratedWholeRestartStandingCellEffectAt (.pending debt)

/-- The total effect is generated by the current raw contact effect and the
unique incoming debt.  It accepts no branch selector or payment witness. -/
noncomputable def generatedWholeRestartStandingCellEffect
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (standing : GeneratedWholeRestartCellStandingAt current) :
    GeneratedWholeRestartStandingCellEffectAt standing := by
  cases standing with
  | clear =>
      generalize effectEq : current.nextCellEffect = effect
      cases effect with
      | oneCell debit incidence =>
          exact .directOneCell debit incidence effectEq
      | retainedResidual residual =>
          exact .opensResidual residual effectEq
  | pending debt =>
      generalize dispositionEq :
        generatedWholeRestartPendingCellDisposition debt = disposition
      cases disposition with
      | settled settlement =>
          exact .settlesPending debt settlement dispositionEq
      | retained notPaid =>
          by_cases debitPos : 0 <
              current.nextCellEffect.debit.netEnstrophyDebit
          · exact .strictPartialPayment debt notPaid debitPos dispositionEq
          · exact .persistentFailure debt notPaid debitPos dispositionEq

/-- Target standing computed by the total emitter.  In particular,
`opensResidual` has a pending target, so the successor emitter cannot
typecheck another `opensResidual`. -/
noncomputable def GeneratedWholeRestartStandingCellEffectAt.targetStanding
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current} :
    GeneratedWholeRestartStandingCellEffectAt standing →
      GeneratedWholeRestartCellStandingAt current.next
  | .directOneCell _debit _incidence _effectEq => .clear
  | .opensResidual residual _effectEq =>
      .pending (generatedWholeRestartPendingCellOfResidual current residual)
  | .settlesPending _debt _settlement _dispositionEq => .clear
  | .strictPartialPayment debt notPaid _debitPos _dispositionEq =>
      .pending (carryGeneratedWholeRestartPendingCell debt notPaid)
  | .persistentFailure debt notPaid _notPositive _dispositionEq =>
      .pending (carryGeneratedWholeRestartPendingCell debt notPaid)

/-- This emitter is not a second scheduler: exposing its branch commutes
with the existing standing transition. -/
theorem GeneratedWholeRestartStandingCellEffectAt.targetStanding_eq_next
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (effect : GeneratedWholeRestartStandingCellEffectAt standing) :
    effect.targetStanding = standing.next := by
  cases effect with
  | directOneCell debit incidence effectEq =>
      simp [GeneratedWholeRestartStandingCellEffectAt.targetStanding,
        GeneratedWholeRestartCellStandingAt.next, effectEq]
  | opensResidual residual effectEq =>
      simp [GeneratedWholeRestartStandingCellEffectAt.targetStanding,
        GeneratedWholeRestartCellStandingAt.next, effectEq]
  | settlesPending debt settlement dispositionEq =>
      simp [GeneratedWholeRestartStandingCellEffectAt.targetStanding,
        GeneratedWholeRestartCellStandingAt.next, dispositionEq]
  | strictPartialPayment debt notPaid _debitPos dispositionEq =>
      simp [GeneratedWholeRestartStandingCellEffectAt.targetStanding,
        GeneratedWholeRestartCellStandingAt.next, dispositionEq]
  | persistentFailure debt notPaid _notPositive dispositionEq =>
      simp [GeneratedWholeRestartStandingCellEffectAt.targetStanding,
        GeneratedWholeRestartCellStandingAt.next, dispositionEq]

/-! ## Standing-valued arithmetic material -/

/-- Arithmetic material of the live standing itself.  Its left history is
the current cell only while the standing is clear; once a residual is live,
the left history remains the exact origin anchor until that one debt is paid. -/
def GeneratedWholeRestartCellStandingAt.arithmeticMaterial
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν} :
    GeneratedWholeRestartCellStandingAt current → RootArithmeticMaterialAt
  | .clear => wholeRestartRootArithmeticMaterialAt current.nextContact
  | .pending debt => GeneratedWholeRestartPendingCellArithmeticMaterialAt debt

@[simp] theorem GeneratedWholeRestartCellStandingAt.arithmeticMaterial_whole_cardinalShadow
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (standing : GeneratedWholeRestartCellStandingAt current) :
    standing.arithmeticMaterial.whole.cardinalShadow =
      wholeRestartCoefficientLevel current.nextContact := by
  cases standing with
  | clear =>
      change (WholeRestartContactCellHistoryAt
        current.nextContact).cardinalShadow = _
      exact WholeRestartContactCellHistoryAt_cardinalShadow _
  | pending debt =>
      change (WholeRestartContactCellHistoryAt
        current.nextContact).cardinalShadow = _
      exact WholeRestartContactCellHistoryAt_cardinalShadow _

@[simp] theorem GeneratedWholeRestartCellStandingAt.arithmeticMaterial_left_cardinalShadow
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (standing : GeneratedWholeRestartCellStandingAt current) :
    standing.arithmeticMaterial.left.cardinalShadow =
      standing.anchorLevel := by
  cases standing with
  | clear =>
      change (WholeRestartContactCellHistoryAt
        current.contact).cardinalShadow = _
      exact WholeRestartContactCellHistoryAt_cardinalShadow _
  | pending debt =>
      change (WholeRestartContactCellHistoryAt
        debt.origin.contact).cardinalShadow = _
      exact WholeRestartContactCellHistoryAt_cardinalShadow _

@[simp] theorem GeneratedWholeRestartCellStandingAt.arithmeticMaterial_right_cardinalShadow
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (standing : GeneratedWholeRestartCellStandingAt current) :
      standing.arithmeticMaterial.right.cardinalShadow = 1 := by
  cases standing <;>
    exact WholeRestartContactOnePaidCellHistory_cardinalShadow

/-- The exact per-edge deficit equation before it is packaged into the root
material.  It already includes both arithmetic payment and Real valuation. -/
theorem cellStanding_next_remainingCellDeficit_eq_current_add_payment_sub_debit
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (standing : GeneratedWholeRestartCellStandingAt current) :
    standing.next.remainingCellDeficit =
      standing.remainingCellDeficit + (standing.paymentIncrement : Real) -
        current.nextCellEffect.debit.netEnstrophyDebit := by
  have sourceEq :
      standing.remainingCellDeficit =
        (standing.anchorLevel : Real) - 1 -
          wholeVorticityEuclideanMass current.contact.physicalState := by
    cases standing with
    | clear => rfl
    | pending debt => exact debt.cellDeficit_eq
  have targetEq :
      standing.next.remainingCellDeficit =
        (standing.next.anchorLevel : Real) - 1 -
          wholeVorticityEuclideanMass current.next.contact.physicalState := by
    cases standing.next with
    | clear => rfl
    | pending debt => exact debt.cellDeficit_eq
  rw [sourceEq, targetEq, cellStanding_anchorLevel_next,
    current.nextCellEffect.debit.netEnstrophyDebit_eq,
    current.nextCellEffect.debit.sourcePhysicalState_eq,
    current.nextCellEffect.debit.targetPhysicalState_eq]
  simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact,
    Nat.cast_add]
  rw [next_contact]
  ring_nf
  rfl

/-- Complete operational material emitted from one live standing.  Generic
arithmetic normalization uses this whole structure as provenance; its
arithmetic and Real-valued projections therefore cannot be mixed across
occurrences. -/
structure NativeRestartStandingValuedArithmeticMaterialAt
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (standing : GeneratedWholeRestartCellStandingAt current) : Type where
  private mk ::
  effect : GeneratedWholeRestartStandingCellEffectAt standing
  rawValuedMaterial : NativeRestartValuedArithmeticMaterialAt
    (generatedWholeRestartCanonicalReplay current.contact)
    current.nextContact
  rawValuedMaterial_eq : rawValuedMaterial = current.nextCellEffect.debit
  arithmeticMaterial : RootArithmeticMaterialAt
  arithmeticMaterial_eq : arithmeticMaterial = standing.arithmeticMaterial
  sourceRemainingDeficit : Real
  sourceRemainingDeficit_eq :
    sourceRemainingDeficit = standing.remainingCellDeficit
  targetStanding : GeneratedWholeRestartCellStandingAt current.next
  targetStanding_eq : targetStanding = standing.next
  targetRemainingDeficit : Real
  targetRemainingDeficit_eq :
    targetRemainingDeficit = targetStanding.remainingCellDeficit
  paymentShadow : Nat
  paymentShadow_eq : paymentShadow = standing.paymentIncrement
  deficit_commutes :
    targetRemainingDeficit =
      sourceRemainingDeficit + (paymentShadow : Real) -
        rawValuedMaterial.netEnstrophyDebit

/-- Source-only compiler for the standing-valued material. -/
noncomputable def nativeRestartStandingValuedArithmeticMaterial
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (effect : GeneratedWholeRestartStandingCellEffectAt standing) :
    NativeRestartStandingValuedArithmeticMaterialAt standing where
  effect := effect
  rawValuedMaterial := current.nextCellEffect.debit
  rawValuedMaterial_eq := rfl
  arithmeticMaterial := standing.arithmeticMaterial
  arithmeticMaterial_eq := rfl
  sourceRemainingDeficit := standing.remainingCellDeficit
  sourceRemainingDeficit_eq := rfl
  targetStanding := standing.next
  targetStanding_eq := rfl
  targetRemainingDeficit := standing.next.remainingCellDeficit
  targetRemainingDeficit_eq := rfl
  paymentShadow := standing.paymentIncrement
  paymentShadow_eq := rfl
  deficit_commutes :=
    cellStanding_next_remainingCellDeficit_eq_current_add_payment_sub_debit
      standing

namespace NativeRestartStandingValuedArithmeticMaterialAt

def parallelNormalForm
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing) :
    ParallelIncidenceNormalFormAt material material.arithmeticMaterial :=
  normalizeParallel material material.arithmeticMaterial

def contactTime
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing) : Real :=
  material.rawValuedMaterial.contactTime

theorem contactTime_pos
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing) :
    0 < material.contactTime :=
  material.rawValuedMaterial.contactTime_pos

theorem standing_currentLevel_le_anchorLevel
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (standing : GeneratedWholeRestartCellStandingAt current) :
    wholeRestartCoefficientLevel current.contact ≤ standing.anchorLevel := by
  cases standing with
  | clear => exact le_rfl
  | pending debt => exact debt.currentLevel_le_originLevel

theorem standing_paymentIncrement_le_one
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    (standing : GeneratedWholeRestartCellStandingAt current) :
    standing.paymentIncrement ≤ 1 := by
  cases standing with
  | clear =>
      generalize effectEq : current.nextCellEffect = effect
      cases effect <;>
        simp [GeneratedWholeRestartCellStandingAt.paymentIncrement, effectEq]
  | pending debt =>
      generalize dispositionEq :
        generatedWholeRestartPendingCellDisposition debt = disposition
      cases disposition <;>
        simp [GeneratedWholeRestartCellStandingAt.paymentIncrement,
          dispositionEq]

theorem coefficientLevel_eq_anchor_add_one_of_commutes
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (commutes : material.arithmeticMaterial.whole =
      material.arithmeticMaterial.left.parallel
        material.arithmeticMaterial.right) :
    wholeRestartCoefficientLevel current.nextContact =
      standing.anchorLevel + 1 := by
  have shadow := congrArg UnitHistory.cardinalShadow commutes
  rw [material.arithmeticMaterial_eq] at shadow
  simpa only [UnitHistory.cardinalShadow_parallel,
    GeneratedWholeRestartCellStandingAt.arithmeticMaterial_whole_cardinalShadow,
    GeneratedWholeRestartCellStandingAt.arithmeticMaterial_left_cardinalShadow,
    GeneratedWholeRestartCellStandingAt.arithmeticMaterial_right_cardinalShadow]
      using shadow

theorem paymentShadow_eq_one_of_commutes
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (commutes : material.arithmeticMaterial.whole =
      material.arithmeticMaterial.left.parallel
        material.arithmeticMaterial.right) :
    material.paymentShadow = 1 := by
  have levelEq := material.coefficientLevel_eq_anchor_add_one_of_commutes
    commutes
  have targetLevelLeAnchor :=
    standing_currentLevel_le_anchorLevel standing.next
  change wholeRestartCoefficientLevel current.nextContact ≤
    standing.next.anchorLevel at targetLevelLeAnchor
  rw [cellStanding_anchorLevel_next] at targetLevelLeAnchor
  have incrementLe := standing_paymentIncrement_le_one standing
  have oneLeIncrement : 1 ≤ standing.paymentIncrement := by
    rw [levelEq] at targetLevelLeAnchor
    omega
  rw [material.paymentShadow_eq]
  exact Nat.le_antisymm incrementLe oneLeIncrement

theorem targetStanding_eq_clear_of_commutes
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (commutes : material.arithmeticMaterial.whole =
      material.arithmeticMaterial.left.parallel
        material.arithmeticMaterial.right) :
    material.targetStanding = .clear := by
  have payment := material.paymentShadow_eq_one_of_commutes commutes
  rw [material.paymentShadow_eq] at payment
  rw [material.targetStanding_eq]
  cases standing with
  | clear =>
      generalize effectEq : current.nextCellEffect = effect
      cases effect with
      | oneCell =>
          simp [GeneratedWholeRestartCellStandingAt.next, effectEq]
      | retainedResidual =>
          simp [GeneratedWholeRestartCellStandingAt.paymentIncrement,
            effectEq] at payment
  | pending debt =>
      generalize dispositionEq :
        generatedWholeRestartPendingCellDisposition debt = disposition
      cases disposition with
      | settled =>
          simp [GeneratedWholeRestartCellStandingAt.next, dispositionEq]
      | retained =>
          simp [GeneratedWholeRestartCellStandingAt.paymentIncrement,
            dispositionEq] at payment

theorem commutes_of_paymentShadow_eq_one
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (payment : material.paymentShadow = 1) :
    material.arithmeticMaterial.whole =
      material.arithmeticMaterial.left.parallel
        material.arithmeticMaterial.right := by
  rw [material.paymentShadow_eq] at payment
  cases standing with
  | clear =>
      generalize effectEq : current.nextCellEffect = effect
      cases effect with
      | oneCell debit exact =>
          rw [material.arithmeticMaterial_eq]
          have exact' := exact
          unfold GeneratedWholeRestartCellDebitAt.ExactValuedOneCellAt at exact'
          rw [debit.arithmeticMaterial_eq] at exact'
          simpa only [GeneratedWholeRestartCellStandingAt.arithmeticMaterial]
            using exact'
      | retainedResidual residual =>
          simp [GeneratedWholeRestartCellStandingAt.paymentIncrement,
            effectEq] at payment
  | pending debt =>
      generalize dispositionEq :
        generatedWholeRestartPendingCellDisposition debt = disposition
      cases disposition with
      | settled settlement =>
          rw [material.arithmeticMaterial_eq]
          have incidence := settlement.incidence
          change
            (GeneratedWholeRestartPendingCellArithmeticMaterialAt debt).whole =
              (GeneratedWholeRestartPendingCellArithmeticMaterialAt debt
                ).left.parallel
                (GeneratedWholeRestartPendingCellArithmeticMaterialAt debt
                  ).right at incidence
          simpa only [GeneratedWholeRestartCellStandingAt.arithmeticMaterial]
            using incidence
      | retained notPaid =>
          simp [GeneratedWholeRestartCellStandingAt.paymentIncrement,
            dispositionEq] at payment

theorem paymentShadow_eq_zero_of_residual
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (residual : GeneratedParallelResidualAt
      material material.arithmeticMaterial) :
    material.paymentShadow = 0 := by
  have shadowLe : material.paymentShadow ≤ 1 := by
    rw [material.paymentShadow_eq]
    exact standing_paymentIncrement_le_one standing
  have shadowNe : material.paymentShadow ≠ 1 := by
    intro shadowOne
    exact residual.mismatch (material.commutes_of_paymentShadow_eq_one shadowOne)
  omega

theorem targetStanding_anchorLevel_eq_source_of_residual
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (residual : GeneratedParallelResidualAt material material.arithmeticMaterial) :
    material.targetStanding.anchorLevel = standing.anchorLevel := by
  have shadowZero := material.paymentShadow_eq_zero_of_residual residual
  rw [material.paymentShadow_eq] at shadowZero
  rw [material.targetStanding_eq, cellStanding_anchorLevel_next, shadowZero]
  omega

theorem targetStanding_is_pending_of_residual
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (residual : GeneratedParallelResidualAt material material.arithmeticMaterial) :
    ∃ debt : GeneratedWholeRestartPendingCellAt current.next,
      material.targetStanding = .pending debt := by
  have shadowZero := material.paymentShadow_eq_zero_of_residual residual
  rw [material.paymentShadow_eq] at shadowZero
  rw [material.targetStanding_eq]
  cases standing with
  | clear =>
      generalize effectEq : current.nextCellEffect = effect
      cases effect with
      | oneCell =>
          simp [GeneratedWholeRestartCellStandingAt.paymentIncrement,
            effectEq] at shadowZero
      | retainedResidual retained =>
          exact ⟨generatedWholeRestartPendingCellOfResidual current retained,
            by simp [GeneratedWholeRestartCellStandingAt.next, effectEq]⟩
  | pending debt =>
      generalize dispositionEq :
        generatedWholeRestartPendingCellDisposition debt = disposition
      cases disposition with
      | settled =>
          simp [GeneratedWholeRestartCellStandingAt.paymentIncrement,
            dispositionEq] at shadowZero
      | retained notPaid =>
          exact ⟨carryGeneratedWholeRestartPendingCell debt notPaid,
            by simp [GeneratedWholeRestartCellStandingAt.next,
              dispositionEq]⟩

/-- Canonical fresh-gain inventory of one valued residual.  Only rows whose
actual target coefficient mass strictly exceeds their source mass are kept;
the finite radius is fixed by the live anchor. -/
noncomputable def standingValuedFreshGainModes
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing) :
    Finset IntegerWavevector :=
  (wholeRestartModes (standing.anchorLevel + 1)).filter fun wave =>
    complexCoordinateAmplitudeSq
        (material.rawValuedMaterial.sourcePhysicalState wave) <
      complexCoordinateAmplitudeSq
        (material.rawValuedMaterial.targetPhysicalState wave)

/-- Emptiness of the generated inventory is exactly coordinatewise
nonincrease on the live anchor cube.  This is the coefficient-level source
obligation exposed by a silent valued residual. -/
theorem standingValuedFreshGainModes_eq_empty_iff
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing) :
    standingValuedFreshGainModes material = ∅ ↔
      ∀ wave ∈ wholeRestartModes (standing.anchorLevel + 1),
        complexCoordinateAmplitudeSq
            (material.rawValuedMaterial.targetPhysicalState wave) ≤
          complexCoordinateAmplitudeSq
            (material.rawValuedMaterial.sourcePhysicalState wave) := by
  constructor
  · intro modesEmpty wave waveMem
    have waveNotMem : wave ∉ standingValuedFreshGainModes material := by
      rw [modesEmpty]
      simp
    by_contra targetNotLe
    exact waveNotMem (Finset.mem_filter.mpr
      ⟨waveMem, lt_of_not_ge targetNotLe⟩)
  · intro coordinateNonincrease
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨wave, waveMem⟩
    have filtered := Finset.mem_filter.mp waveMem
    exact (not_lt_of_ge (coordinateNonincrease wave filtered.1)) filtered.2

/-- A typed residual generates the next standing-valued arithmetic material
on the compiler-owned successor.  There is no caller-supplied recurrence
program or future material table. -/
structure GeneratedResidualExpansionAt
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (residual : GeneratedParallelResidualAt material material.arithmeticMaterial) :
    Type where
  private mk ::
  nextEffect : GeneratedWholeRestartStandingCellEffectAt material.targetStanding
  nextMaterial : NativeRestartStandingValuedArithmeticMaterialAt
    material.targetStanding
  nextMaterial_eq : nextMaterial =
    nativeRestartStandingValuedArithmeticMaterial nextEffect
  nextRawValuedMaterial_eq : nextMaterial.rawValuedMaterial =
    current.next.nextCellEffect.debit
  nextNormalForm : ParallelIncidenceNormalFormAt
    nextMaterial nextMaterial.arithmeticMaterial
  nextNormalForm_eq : nextNormalForm = nextMaterial.parallelNormalForm
  physicalModes : Finset IntegerWavevector
  physicalModes_eq : physicalModes =
    standingValuedFreshGainModes material
  physicalModes_zeroNotMem : (0 : IntegerWavevector) ∉ physicalModes
  finiteNetEnstrophyDebit : Real
  finiteNetEnstrophyDebit_eq :
    finiteNetEnstrophyDebit =
      finiteStateVorticityCoefficientEnstrophy physicalModes
          material.rawValuedMaterial.targetPhysicalState -
        finiteStateVorticityCoefficientEnstrophy physicalModes
          material.rawValuedMaterial.sourcePhysicalState
  finiteNetEnstrophyDebit_nonneg : 0 ≤ finiteNetEnstrophyDebit
  sourceComplementaryMass : Real
  sourceComplementaryMass_eq :
    sourceComplementaryMass =
      wholeVorticityEuclideanMass
          material.rawValuedMaterial.sourcePhysicalState -
        finiteStateVorticityCoefficientEnstrophy physicalModes
          material.rawValuedMaterial.sourcePhysicalState
  sourceComplementaryMass_nonneg : 0 ≤ sourceComplementaryMass
  targetComplementaryMass : Real
  targetComplementaryMass_eq :
    targetComplementaryMass =
      wholeVorticityEuclideanMass
          material.rawValuedMaterial.targetPhysicalState -
        finiteStateVorticityCoefficientEnstrophy physicalModes
          material.rawValuedMaterial.targetPhysicalState
  targetComplementaryMass_nonneg : 0 ≤ targetComplementaryMass
  valuation_commutes :
    finiteNetEnstrophyDebit -
        material.rawValuedMaterial.netEnstrophyDebit =
      sourceComplementaryMass - targetComplementaryMass

noncomputable def generatedResidualExpansion
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (residual : GeneratedParallelResidualAt material material.arithmeticMaterial) :
    GeneratedResidualExpansionAt material residual := by
  let nextEffect := generatedWholeRestartStandingCellEffect material.targetStanding
  let physicalModes := standingValuedFreshGainModes material
  exact
    { nextEffect := nextEffect
      nextMaterial := nativeRestartStandingValuedArithmeticMaterial nextEffect
      nextMaterial_eq := rfl
      nextRawValuedMaterial_eq := rfl
      nextNormalForm :=
        (nativeRestartStandingValuedArithmeticMaterial nextEffect
          ).parallelNormalForm
      nextNormalForm_eq := rfl
      physicalModes := physicalModes
      physicalModes_eq := rfl
      physicalModes_zeroNotMem := by
        change (0 : IntegerWavevector) ∉
          standingValuedFreshGainModes material
        intro zeroMem
        have cubeMem : (0 : IntegerWavevector) ∈
            wholeRestartModes (standing.anchorLevel + 1) :=
          (Finset.mem_filter.mp zeroMem).1
        exact (zero_not_mem_puncturedIntegerWaveFrequencyCube _) cubeMem
      finiteNetEnstrophyDebit :=
        finiteStateVorticityCoefficientEnstrophy physicalModes
            material.rawValuedMaterial.targetPhysicalState -
          finiteStateVorticityCoefficientEnstrophy physicalModes
            material.rawValuedMaterial.sourcePhysicalState
      finiteNetEnstrophyDebit_eq := rfl
      finiteNetEnstrophyDebit_nonneg := by
        change 0 ≤
          finiteStateVorticityCoefficientEnstrophy
              (standingValuedFreshGainModes material)
              material.rawValuedMaterial.targetPhysicalState -
            finiteStateVorticityCoefficientEnstrophy
              (standingValuedFreshGainModes material)
              material.rawValuedMaterial.sourcePhysicalState
        apply sub_nonneg.mpr
        unfold finiteStateVorticityCoefficientEnstrophy
        apply Finset.sum_le_sum
        intro wave waveMem
        exact (Finset.mem_filter.mp waveMem).2.le
      sourceComplementaryMass :=
        wholeVorticityEuclideanMass
            material.rawValuedMaterial.sourcePhysicalState -
          finiteStateVorticityCoefficientEnstrophy physicalModes
            material.rawValuedMaterial.sourcePhysicalState
      sourceComplementaryMass_eq := rfl
      sourceComplementaryMass_nonneg := by
        apply sub_nonneg.mpr
        exact
          ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
            physicalModes material.rawValuedMaterial.sourcePhysicalState
      targetComplementaryMass :=
        wholeVorticityEuclideanMass
            material.rawValuedMaterial.targetPhysicalState -
          finiteStateVorticityCoefficientEnstrophy physicalModes
            material.rawValuedMaterial.targetPhysicalState
      targetComplementaryMass_eq := rfl
      targetComplementaryMass_nonneg := by
        apply sub_nonneg.mpr
        exact
          ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
            physicalModes material.rawValuedMaterial.targetPhysicalState
      valuation_commutes := by
        rw [material.rawValuedMaterial.netEnstrophyDebit_eq]
        ring }

theorem GeneratedResidualExpansionAt.physicalModes_eq_freshGainModes
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    {material : NativeRestartStandingValuedArithmeticMaterialAt standing}
    {residual : GeneratedParallelResidualAt material material.arithmeticMaterial}
    (expansion : GeneratedResidualExpansionAt material residual) :
    expansion.physicalModes = standingValuedFreshGainModes material :=
  expansion.physicalModes_eq

/-- The generated finite valuation is strictly positive exactly when the
same occurrence actually contains a fresh-gain Fourier row.  Thus positivity
is not a second scalar obligation detached from the arithmetic material. -/
theorem GeneratedResidualExpansionAt.finiteNetEnstrophyDebit_pos_iff_modes_nonempty
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    {material : NativeRestartStandingValuedArithmeticMaterialAt standing}
    {residual : GeneratedParallelResidualAt material material.arithmeticMaterial}
    (expansion : GeneratedResidualExpansionAt material residual) :
    0 < expansion.finiteNetEnstrophyDebit ↔
      expansion.physicalModes.Nonempty := by
  rw [expansion.finiteNetEnstrophyDebit_eq]
  constructor
  · intro debitPos
    by_contra modesNotNonempty
    have modesEmpty : expansion.physicalModes = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp modesNotNonempty
    rw [modesEmpty] at debitPos
    unfold finiteStateVorticityCoefficientEnstrophy at debitPos
    have zeroLtZero : (0 : Real) < 0 := by
      simpa only [Finset.sum_empty, sub_self] using debitPos
    exact (lt_irrefl 0) zeroLtZero
  · intro modesNonempty
    apply sub_pos.mpr
    unfold finiteStateVorticityCoefficientEnstrophy
    apply Finset.sum_lt_sum_of_nonempty modesNonempty
    intro wave waveMem
    have freshMem : wave ∈ standingValuedFreshGainModes material := by
      rw [← expansion.physicalModes_eq]
      exact waveMem
    exact (Finset.mem_filter.mp freshMem).2

/-- The silent physical face is definitionally the empty fresh-gain
inventory of this exact material occurrence. -/
theorem GeneratedResidualExpansionAt.finiteNetEnstrophyDebit_eq_zero_iff_modes_empty
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    {material : NativeRestartStandingValuedArithmeticMaterialAt standing}
    {residual : GeneratedParallelResidualAt material material.arithmeticMaterial}
    (expansion : GeneratedResidualExpansionAt material residual) :
    expansion.finiteNetEnstrophyDebit = 0 ↔
      expansion.physicalModes = ∅ := by
  constructor
  · intro debitZero
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro modesNonempty
    have debitPos :=
      expansion.finiteNetEnstrophyDebit_pos_iff_modes_nonempty.mpr
        modesNonempty
    linarith
  · intro modesEmpty
    have debitNotPos : ¬ 0 < expansion.finiteNetEnstrophyDebit := by
      intro debitPos
      have modesNonempty :=
        expansion.finiteNetEnstrophyDebit_pos_iff_modes_nonempty.mp
          debitPos
      rw [modesEmpty] at modesNonempty
      exact Finset.not_nonempty_empty modesNonempty
    exact le_antisymm (le_of_not_gt debitNotPos)
      expansion.finiteNetEnstrophyDebit_nonneg

/-- A silent expansion is therefore not an opaque Real branch: it is the
exact statement that no Fourier row in the live anchor cube gained amplitude
mass on this actual source update. -/
theorem GeneratedResidualExpansionAt.finiteNetEnstrophyDebit_eq_zero_iff_coordinatewise_nonincrease
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    {material : NativeRestartStandingValuedArithmeticMaterialAt standing}
    {residual : GeneratedParallelResidualAt material material.arithmeticMaterial}
    (expansion : GeneratedResidualExpansionAt material residual) :
    expansion.finiteNetEnstrophyDebit = 0 ↔
      ∀ wave ∈ wholeRestartModes (standing.anchorLevel + 1),
        complexCoordinateAmplitudeSq
            (material.rawValuedMaterial.targetPhysicalState wave) ≤
          complexCoordinateAmplitudeSq
            (material.rawValuedMaterial.sourcePhysicalState wave) := by
  rw [expansion.finiteNetEnstrophyDebit_eq_zero_iff_modes_empty,
    expansion.physicalModes_eq,
    standingValuedFreshGainModes_eq_empty_iff]

/-- Arithmetic remaining debt and complementary physical mass are the two
projections of one residual settlement.  This commuting law lives on the
generated expansion carrier, before any root obstruction subtype is read. -/
theorem GeneratedResidualExpansionAt.hybridDebt_commutes
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    {material : NativeRestartStandingValuedArithmeticMaterialAt standing}
    {residual : GeneratedParallelResidualAt material material.arithmeticMaterial}
    (expansion : GeneratedResidualExpansionAt material residual) :
    material.targetRemainingDeficit + expansion.targetComplementaryMass =
      material.sourceRemainingDeficit + expansion.sourceComplementaryMass -
        expansion.finiteNetEnstrophyDebit := by
  have deficit := material.deficit_commutes
  rw [material.paymentShadow_eq_zero_of_residual residual] at deficit
  norm_num at deficit
  linarith [expansion.valuation_commutes]

/-- Real-valued physical normal form of the same generated expansion.  It is
indexed by the expansion carrier itself and therefore cannot be paired with
another occurrence's arithmetic residual. -/
inductive GeneratedResidualExpansionAt.PhysicalValuationNormalFormAt
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    {material : NativeRestartStandingValuedArithmeticMaterialAt standing}
    {residual : GeneratedParallelResidualAt material material.arithmeticMaterial}
    (expansion : GeneratedResidualExpansionAt material residual) : Type
  | positive
      (debit_pos : 0 < expansion.finiteNetEnstrophyDebit)
  | silent
      (debit_eq_zero : expansion.finiteNetEnstrophyDebit = 0)

noncomputable def GeneratedResidualExpansionAt.physicalValuationNormalForm
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    {material : NativeRestartStandingValuedArithmeticMaterialAt standing}
    {residual : GeneratedParallelResidualAt material material.arithmeticMaterial}
    (expansion : GeneratedResidualExpansionAt material residual) :
    expansion.PhysicalValuationNormalFormAt := by
  by_cases debitPos : 0 < expansion.finiteNetEnstrophyDebit
  · exact .positive debitPos
  · exact .silent (le_antisymm (le_of_not_gt debitPos)
      expansion.finiteNetEnstrophyDebit_nonneg)

theorem netEnstrophyDebit_pos_of_commutes
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (commutes : material.arithmeticMaterial.whole =
      material.arithmeticMaterial.left.parallel
        material.arithmeticMaterial.right) :
    0 < material.rawValuedMaterial.netEnstrophyDebit := by
  have levelEq := material.coefficientLevel_eq_anchor_add_one_of_commutes
    commutes
  have sourceMassLe :
      wholeVorticityEuclideanMass current.contact.physicalState ≤
        (standing.anchorLevel : Real) - 1 := by
    have remainingNonneg := standing.remainingCellDeficit_nonneg
    rw [standing.remainingCellDeficit_eq_anchorLevel_sub_physicalMass]
      at remainingNonneg
    linarith
  have anchorLtTargetLevel :
      standing.anchorLevel <
        wholeRestartCoefficientLevel current.nextContact := by omega
  have anchorLtTargetRaw :
      (standing.anchorLevel : Real) <
        wholeRestartRawCoefficientCeiling current.nextContact :=
    (Nat.lt_ceil).1 anchorLtTargetLevel
  rw [wholeRestartRawCoefficientCeiling_eq] at anchorLtTargetRaw
  simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    at anchorLtTargetRaw
  have sourceMassLtTargetMass :
      wholeVorticityEuclideanMass current.contact.physicalState <
        wholeVorticityEuclideanMass current.nextContact.physicalState := by
    linarith
  rw [material.rawValuedMaterial.netEnstrophyDebit_eq,
    material.rawValuedMaterial.sourcePhysicalState_eq,
    material.rawValuedMaterial.targetPhysicalState_eq]
  simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
  exact sub_pos.mpr sourceMassLtTargetMass

theorem targetRemainingDeficit_lt_source_of_residual_of_debit_pos
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (residual : GeneratedParallelResidualAt material material.arithmeticMaterial)
    (debitPos : 0 < material.rawValuedMaterial.netEnstrophyDebit) :
    material.targetRemainingDeficit < material.sourceRemainingDeficit := by
  have shadowZero := material.paymentShadow_eq_zero_of_residual residual
  have commuting := material.deficit_commutes
  rw [shadowZero] at commuting
  norm_num at commuting
  linarith

theorem obstructionLiability_eq_targetRemaining_sub_source
    {ν : Viscosity}
    {current : GeneratedWholeRestartCurrent ν}
    {standing : GeneratedWholeRestartCellStandingAt current}
    (material : NativeRestartStandingValuedArithmeticMaterialAt standing)
    (residual : GeneratedParallelResidualAt material material.arithmeticMaterial)
    (debitNonpos : material.rawValuedMaterial.netEnstrophyDebit ≤ 0) :
    0 ≤ -material.rawValuedMaterial.netEnstrophyDebit ∧
      -material.rawValuedMaterial.netEnstrophyDebit =
        material.targetRemainingDeficit - material.sourceRemainingDeficit := by
  have shadowZero := material.paymentShadow_eq_zero_of_residual residual
  have commuting := material.deficit_commutes
  rw [shadowZero] at commuting
  norm_num at commuting
  constructor <;> linarith

end NativeRestartStandingValuedArithmeticMaterialAt

/-- Runtime current carrying both the physical NS state and its unique cell
standing. -/
structure GeneratedWholeRestartRuntimeCurrent (ν : Viscosity) : Type where
  physical : GeneratedWholeRestartCurrent ν
  standing : GeneratedWholeRestartCellStandingAt physical
  cellEffect : GeneratedWholeRestartStandingCellEffectAt standing

noncomputable def GeneratedWholeRestartRuntimeCurrent.next
    {ν : Viscosity}
    (current : GeneratedWholeRestartRuntimeCurrent ν) :
    GeneratedWholeRestartRuntimeCurrent ν where
  physical := current.physical.next
  standing := current.standing.next
  cellEffect := generatedWholeRestartStandingCellEffect current.standing.next

/-- Residual-aware runtime readout.  Initial standing is clear.  Every live
debt is revalued by every subsequent actual source action; a nonpositive edge
is exposed as an obstruction effect but does not freeze later occurrences. -/
noncomputable def runRuntime
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    ℕ → GeneratedWholeRestartRuntimeCurrent ν
  | 0 => ⟨initial, .clear,
      generatedWholeRestartStandingCellEffect .clear⟩
  | index + 1 => (runRuntime initial index).next

/-- Physical projection of the residual-aware runtime.  This preserves the
historical `run` mouth while making its cell standing source-generated. -/
noncomputable def run
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : GeneratedWholeRestartCurrent ν :=
  (runRuntime initial index).physical

@[simp] theorem run_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    run initial 0 = initial := rfl

@[simp] theorem run_succ
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    run initial (index + 1) = (run initial index).next := rfl

/-- Cell standing at one exact physical run occurrence. -/
noncomputable def runCellStanding
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : GeneratedWholeRestartCellStandingAt (run initial index) :=
  (runRuntime initial index).standing

/-- Complete standing-aware cell effect carried by the exact run current.
After an `opensResidual` target becomes pending, this dependent type admits
only settlement, strict partial payment, or persistent failure. -/
noncomputable def runStandingCellEffect
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    GeneratedWholeRestartStandingCellEffectAt
      (runCellStanding initial index) :=
  (runRuntime initial index).cellEffect

@[simp] theorem runCellStanding_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    runCellStanding initial 0 = .clear := rfl

@[simp] theorem runCellStanding_succ
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    runCellStanding initial (index + 1) =
      (runCellStanding initial index).next := rfl

/-- Number of unit cells actually discharged by the residual-aware runtime
before one finite stage.  It is generated recursively from the exact
standing transition and contains no future table. -/
noncomputable def runCellPaymentCount
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) : Nat → Nat
  | 0 => 0
  | index + 1 =>
      runCellPaymentCount initial index +
        (runCellStanding initial index).paymentIncrement

@[simp] theorem runCellPaymentCount_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    runCellPaymentCount initial 0 = 0 := rfl

@[simp] theorem runCellPaymentCount_succ
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : Nat) :
    runCellPaymentCount initial (index + 1) =
      runCellPaymentCount initial index +
        (runCellStanding initial index).paymentIncrement := rfl

/-- Exact whole-run fold: the live standing's anchor level is the initial
level plus the number of cells already discharged.  A residual may delay a
unit payment but cannot duplicate it or change its origin. -/
theorem runCellStanding_anchorLevel_eq_initial_add_paymentCount
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    ∀ index : Nat,
      (runCellStanding initial index).anchorLevel =
        wholeRestartCoefficientLevel initial.contact +
          runCellPaymentCount initial index := by
  intro index
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        ((runCellStanding initial index).next).anchorLevel =
          wholeRestartCoefficientLevel initial.contact +
            (runCellPaymentCount initial index +
              (runCellStanding initial index).paymentIncrement)
      rw [cellStanding_anchorLevel_next, inductionHypothesis]
      omega

/-- A source law settling every live debt on the immediately following
action makes the generated payment count grow at least once every two
physical edges. -/
theorem runCellPaymentCount_add_one_le_add_two_of_immediateSettlement
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (immediate : ∀ index : Nat,
      (runCellStanding initial index).IsImmediatelySettled)
    (index : Nat) :
    runCellPaymentCount initial index + 1 ≤
      runCellPaymentCount initial (index + 2) := by
  have pairPayment := cellStanding_twoStepPayment
    (runCellStanding initial index)
    (immediate index)
    (show (runCellStanding initial index).next.IsImmediatelySettled by
      have nextImmediate := immediate (index + 1)
      change (runCellStanding initial index).next.IsImmediatelySettled at nextImmediate
      exact nextImmediate)
  change
    runCellPaymentCount initial index + 1 ≤
      (runCellPaymentCount initial index +
          (runCellStanding initial index).paymentIncrement) +
        (runCellStanding initial (index + 1)).paymentIncrement
  change
    runCellPaymentCount initial index + 1 ≤
      (runCellPaymentCount initial index +
          (runCellStanding initial index).paymentIncrement) +
        (runCellStanding initial index).next.paymentIncrement
  omega

theorem index_div_two_le_runCellPaymentCount_of_immediateSettlement
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (immediate : ∀ index : Nat,
      (runCellStanding initial index).IsImmediatelySettled) :
    ∀ index : Nat,
      index / 2 ≤ runCellPaymentCount initial index := by
  intro index
  induction index using Nat.twoStepInduction with
  | zero => simp
  | one => simp [runCellPaymentCount]
  | more index inductionHypothesis _nextHypothesis =>
      have step :=
        runCellPaymentCount_add_one_le_add_two_of_immediateSettlement
          initial immediate index
      omega

/-- Exact scale consequence of immediate same-debt settlement.  The bound
uses the actual level at every physical stage, including residual stages. -/
theorem index_div_two_le_runCoefficientLevel_of_immediateSettlement
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (immediate : ∀ index : Nat,
      (runCellStanding initial index).IsImmediatelySettled)
    (index : Nat) :
    index / 2 ≤
      wholeRestartCoefficientLevel (run initial index).contact := by
  have currentLevelEq :=
    cellStanding_currentLevel_eq_anchorLevel_of_immediatelySettled
      (runCellStanding initial index) (immediate index)
  have anchorFold :=
    runCellStanding_anchorLevel_eq_initial_add_paymentCount initial index
  have countLower :=
    index_div_two_le_runCellPaymentCount_of_immediateSettlement
      initial immediate index
  rw [currentLevelEq, anchorFold]
  omega

/-- Complete source-generated edge at one actual run stage. -/
noncomputable def runGeneratedNext
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    GeneratedWholeRestartNextAt (run initial index) :=
  (run initial index).generatedNext

/-- The run consumes the emitter's total cell effect on every generated
edge; this is the same contact sequence used by `run`, not a parallel
scheduler. -/
noncomputable def runCellEffect
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    GeneratedWholeRestartCellEffectAt
      (run initial index).nextContact :=
  (runGeneratedNext initial index).cellEffect

/-- Runtime projection of the standing-valued material's exact deficit row. -/
theorem run_remainingCellDeficit_succ_eq_current_add_payment_sub_debit
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (stage : Nat) :
    (runCellStanding initial (stage + 1)).remainingCellDeficit =
      (runCellStanding initial stage).remainingCellDeficit +
          ((runCellStanding initial stage).paymentIncrement : Real) -
        (runCellEffect initial stage).debit.netEnstrophyDebit :=
  cellStanding_next_remainingCellDeficit_eq_current_add_payment_sub_debit
    (runCellStanding initial stage)

/-- Exact finite-prefix normalization fold of the source-generated valued
materials. -/
theorem run_sum_netEnstrophyDebit_eq_initialRemaining_add_paymentCount_sub_remaining
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    ∀ length : Nat,
      (∑ stage ∈ Finset.range length,
          (runCellEffect initial stage).debit.netEnstrophyDebit) =
        (runCellStanding initial 0).remainingCellDeficit +
          (runCellPaymentCount initial length : Real) -
          (runCellStanding initial length).remainingCellDeficit := by
  intro length
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis,
        runCellPaymentCount_succ,
        run_remainingCellDeficit_succ_eq_current_add_payment_sub_debit]
      norm_num [Nat.cast_add]
      ring

/-- Exact whole-run arithmetic/physical commuting read directly from the
standing-valued carrier. -/
theorem run_physicalMass_add_remainingCellDeficit_eq_initialLevel_add_paymentCount
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (stage : Nat) :
    wholeVorticityEuclideanMass
          (run initial stage).contact.physicalState + 1 +
        (runCellStanding initial stage).remainingCellDeficit =
      (wholeRestartCoefficientLevel initial.contact : Real) +
        (runCellPaymentCount initial stage : Real) := by
  have remainingEq :=
    (runCellStanding initial stage
      ).remainingCellDeficit_eq_anchorLevel_sub_physicalMass
  have anchorFold :=
    runCellStanding_anchorLevel_eq_initial_add_paymentCount initial stage
  have anchorFoldReal := congrArg (fun value : Nat => (value : Real)) anchorFold
  norm_num [Nat.cast_add] at anchorFoldReal
  rw [remainingEq, anchorFoldReal]
  ring

/-- Public no-free-parameter exhaustion on every actual native restart
segment.  The theorem does not ask a caller to choose the crossing branch
or provide a critical margin. -/
theorem run_nextContact_halfCriticalAbsorption_disposition
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 <
        criticalEnstrophyLatticeConstant *
          wholeVorticityEuclideanMass
            (run initial index).contact.physicalState ∨
      wholeVorticityEuclideanMass
            (run initial index).nextContact.physicalState +
          2 * criticalEnstrophyAbsorptionCoefficient (1 / 2) ν *
            wholePrefixVorticityGradientMass
              (run initial index).nextContact.time
              (run initial index).nextReceipt.stateLimit ≤
        wholeVorticityEuclideanMass
          (run initial index).contact.physicalState :=
  (run initial index).nextContact_halfCriticalAbsorption_disposition

/-- Adjacent generated receipts glue on the exact whole physical state. -/
theorem run_succ_initialState
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    (run initial (index + 1)).initialState =
      (run initial index).contact.physicalState := rfl

/-- At every generated stage, the receipt starts from that stage's exact
whole physical current. -/
theorem run_receipt_initial
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    (run initial index).receipt.wholePath
        ⟨0, ⟨le_rfl, (run initial index).receipt.requestedTimePos.le⟩⟩ =
      (run initial index).initialState :=
  (run initial index).receipt.wholePath_initial

/-- Every generated edge has strictly positive physical duration. -/
theorem run_contact_time_pos
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    0 < (run initial index).contact.time.1 :=
  (run initial index).contact.time_pos

/-- Every generated edge consumes more than half of the source-generated
local whole-flow horizon.  Hence a finite-time accumulation cannot be an
artifact of repeatedly selecting contacts arbitrarily close to time zero. -/
theorem run_contact_time_half_duration_lt
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    (run initial index).duration / 2 <
      (run initial index).contact.time.1 :=
  (run initial index).contact.time_half_lt

/-- Kinetic-scale mass is paid once across every exact adjacent restart
edge; restart coordinates do not create a second energy charge. -/
theorem run_contact_kineticMass_succ_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    puncturedWholeVorticityKineticMass
        (run initial (index + 1)).contact.physicalState ≤
      puncturedWholeVorticityKineticMass
        (run initial index).contact.physicalState := by
  rw [run_succ]
  change
    puncturedWholeVorticityKineticMass
        (run initial index).nextContact.physicalState ≤
      puncturedWholeVorticityKineticMass
        (run initial index).contact.physicalState
  exact nextContact_kineticMass_le (run initial index)

/-- The whole generated contact chain carries one antitone physical kinetic
ledger, with no caller cutoff or restart-payment certificate. -/
theorem run_contact_kineticMass_antitone
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    Antitone fun index =>
      puncturedWholeVorticityKineticMass
        (run initial index).contact.physicalState :=
  antitone_nat_of_succ_le
    (run_contact_kineticMass_succ_le initial)

/-- Accumulated physical time of the generated write-chain. -/
def elapsedTime
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) : ℕ → ℝ
  | 0 => 0
  | index + 1 =>
      elapsedTime initial index + (run initial index).contact.time.1

@[simp] theorem elapsedTime_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    elapsedTime initial 0 = 0 := rfl

@[simp] theorem elapsedTime_succ
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    elapsedTime initial (index + 1) =
      elapsedTime initial index + (run initial index).contact.time.1 := rfl

/-- The generated write-chain advances strictly on the physical time axis. -/
theorem elapsedTime_strictMono
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    StrictMono (elapsedTime initial) := by
  apply strictMono_nat_of_lt_succ
  intro index
  rw [elapsedTime_succ]
  linarith [run_contact_time_pos initial index]

/-- Accumulated physical time is exactly the sum of the actual source-owned
contact times, with no hidden restart interval or duplicate charge. -/
theorem elapsedTime_eq_sum_contactTime
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    ∀ length : ℕ,
      elapsedTime initial length =
        ∑ index ∈ Finset.range length,
          (run initial index).contact.time.1
  | 0 => by simp
  | length + 1 => by
      rw [elapsedTime_succ,
        elapsedTime_eq_sum_contactTime initial length,
        Finset.sum_range_succ]

theorem elapsedTime_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) :
    0 ≤ elapsedTime initial length := by
  rw [elapsedTime_eq_sum_contactTime]
  exact Finset.sum_nonneg fun index indexMem =>
    (run_contact_time_pos initial index).le

/-- A uniform positive lower bound on the actual local whole horizons forces
the generated physical time axis to be unbounded. -/
theorem not_bddAbove_elapsedTime_of_duration_lower_bound
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    {lower : ℝ}
    (lowerPos : 0 < lower)
    (durationLower :
      ∀ index : ℕ, lower ≤ (run initial index).duration) :
    ¬ BddAbove (Set.range (elapsedTime initial)) := by
  rintro ⟨upper, upperBound⟩
  obtain ⟨length : ℕ, lengthLarge⟩ :=
    exists_nat_gt (2 * max upper 0 / lower)
  have eachLower :
      ∀ index ∈ Finset.range length,
        lower / 2 ≤ (run initial index).contact.time.1 := by
    intro index indexMem
    have contactLate :=
      run_contact_time_half_duration_lt initial index
    have horizonLower := durationLower index
    linarith
  have elapsedLower :
      (length : ℝ) * (lower / 2) ≤
        elapsedTime initial length := by
    rw [elapsedTime_eq_sum_contactTime]
    calc
      (length : ℝ) * (lower / 2) =
          ∑ _index ∈ Finset.range length, lower / 2 := by simp
      _ ≤ _ := Finset.sum_le_sum eachLower
  have upperAt : elapsedTime initial length ≤ upper :=
    upperBound ⟨length, rfl⟩
  have maxUpperLt :
      max upper 0 < (length : ℝ) * (lower / 2) := by
    have scaled :
        2 * max upper 0 < (length : ℝ) * lower := by
      exact (div_lt_iff₀ lowerPos).mp lengthLarge
    nlinarith
  linarith [le_max_left upper 0]

/-- Therefore every finite-time generated write-chain forces its actual
local whole horizons to become arbitrarily small. -/
theorem duration_arbitrarily_small_of_elapsedTime_bddAbove
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ∀ ε : ℝ, 0 < ε →
      ∃ index : ℕ, (run initial index).duration < ε := by
  intro ε εPos
  by_contra noSmall
  push Not at noSmall
  exact
    (not_bddAbove_elapsedTime_of_duration_lower_bound
      initial εPos noSmall) elapsedBounded

end GeneratedWholeRestartCurrent

/-- The original native macro contact as the first whole-flow current. -/
noncomputable def generatedNativeMacroWholeRestartCurrentAt
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    GeneratedWholeRestartCurrent ν where
  initialState := recollectedPhysicalState (lineage.current index)
  duration := sourceOwnedLocalReplayV2Duration (dropLineage lineage index)
  receipt := generatedNativeMacroWholeUnforcedLocalUpdateAt lineage index
  contact := generatedNativeMacroWholePositiveTimeRestartContactAt lineage index

/-- Source-facing infinite whole-flow write-chain from one actual native
macro occurrence. -/
noncomputable def generatedNativeMacroWholeRestartRunAt
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    ℕ → GeneratedWholeRestartCurrent ν :=
  GeneratedWholeRestartCurrent.run
    (generatedNativeMacroWholeRestartCurrentAt lineage index)

end

end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
end NavierStokes
end SaturationMonoid
