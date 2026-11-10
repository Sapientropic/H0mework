import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleSourceFilter
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleWindowRead

/-! The fixed-event causal window read transported to the completed sourceFilter
history carrier, through the generated pole/approach states. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3SourceEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse
open PreparationVacuumUncutYukawa PreparationVacuumSourcePreparedResponse
open GaussComposite.SourceGraph
open ActualDressedUniformMaterialCoefficients ActualElectronPhysicalJointInverse
open ActualElectronWholeChargeSoft CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization
open SourceFamilyHilbert SourceFamilyOperator
open SourcePropagationAlgebraicResponse SourcePropagationCommonMomentum
open LowEnergy.ActualDressedVisiblePole
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalFeedback
open PreparationVacuumRawJointFeedback PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumNoetherChart PreparationVacuumGaugeSourceInjection
open PreparationVacuumFieldPerturbation.Blocks PreparationVacuumFullPoleContinuation
open ActualEMJointCurrentMomentum ActualElectronWholeChargeSoft
open ActualElectronWholeNoetherObserver ActualDressedFullCoulomb ActualDressedNoether
open ActualElectronFullNoetherMixedSoft SourceFamilyHilbert SourceFamilyOperator
open SourcePropagationTimeDependentFeedback
open PhysicalN3CausalWindow ActualSourceLightCircuit
open Filter
open scoped InnerProductSpace Topology

attribute [local irreducible] actualElectronPhysicalSeed actualElectronPhysicalResponse
  materialJointNumerator jointGenerator jointResolvent jointPolynomial compressionPolynomial
  physicalN3InputEnergyRead physicalN3InputEnergyNumerator
  physicalN3OutputEnergyNumerator physicalN3OutputEnergyGerm actualElectronPhysicalUnit
  physicalN3OutputPoleOrder physicalN3OutputPoleLeading physicalN3OutputPoleUnit
  actualElectronPhysicalChargeCorrection chargeReader actualElectronPhysicalState
  actualElectronPhysicalStateFamily actualNoetherBackground
  physicalN3PolePhase physicalN3PoleEnergyRadius physicalN3PoleEnergyScale
  physicalN3PoleApproachEnergy physicalN3PoleApproachUnit
  physicalN3ResponseWindowOperator sourceProjectedWindowOperator laplaceWeight
  sourceRestLightMap sourceRestRemainderMap sourceProjectedVariation
  actualFullNoetherVariation prepared sourceProfile physicalN3ExternalEnergyFrameRead

/-- Constant families embed into the completion exactly as the `embed` isometry. -/
private theorem pole_embed_constant {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : Ultrafilter I) (x : E) :
    SourceFamilyHilbert.embed u x =
      (SourceFamilyHilbert.constant u x : SourceFamilyHilbert.Hilbert E u) := rfl

/-- The whole-family observer read returns through the original ultrafilter. -/
private theorem pole_family_observer_return {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : Ultrafilter I)
    (U b : SourceFamilyHilbert.Family E u) (A : SourceFamilyOperator.Operator I E) :
    Tendsto (fun F => -inner ℂ (SourceFamilyHilbert.value U F)
        (A.component F (SourceFamilyHilbert.value U F))+
      inner ℂ (SourceFamilyHilbert.value b F)
        (A.component F (SourceFamilyHilbert.value b F))) u
      (𝓝 (-inner ℂ (U : SourceFamilyHilbert.Hilbert E u)
          (lift u A (U : SourceFamilyHilbert.Hilbert E u))+
        inner ℂ (b : SourceFamilyHilbert.Hilbert E u)
          (lift u A (b : SourceFamilyHilbert.Hilbert E u)))) := by
  rw [lift_coe,lift_coe,inner_coe,inner_coe]
  exact (pair_tendsto u U (act u A U)).neg.add (pair_tendsto u b (act u A b))

/-- The lifted constant reader keeps the original operator norm. -/
private theorem pole_reader_bound {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : Ultrafilter I) (A : E→L[ℂ]E) :
    ‖lift u (SourceFamilyOperator.constant A)‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  exact SourceBoundaryGram.lift_bound_explicit u (SourceFamilyOperator.constant A) ‖A‖
    (norm_nonneg A) (fun _ y=>A.le_opNorm y) x

/-- The lifted constant reader preserves operator sums (generated `constant_add`). -/
private theorem pole_reader_add (A B : H→L[ℂ]H) :
    GaussUnitaryHistory.reader (A+B) =
      GaussUnitaryHistory.reader A + GaussUnitaryHistory.reader B :=
  SourceFamilyOperator.constant_add GaussUnitaryHistory.sourceFilter A B

/-- Pointwise inner split of the lifted sum; proven at the operator-application level
so the public mouths never rewrite under `inner`. -/
private theorem pole_reader_inner_add (A B : H→L[ℂ]H) (x y : ElectronHistory) :
    inner ℂ x (GaussUnitaryHistory.reader (A+B) y) =
      inner ℂ x (GaussUnitaryHistory.reader A y) +
        inner ℂ x (GaussUnitaryHistory.reader B y) := by
  have happ : GaussUnitaryHistory.reader (A+B) y =
      GaussUnitaryHistory.reader A y + GaussUnitaryHistory.reader B y :=
    congrArg (fun R : ElectronHistory →L[ℂ] ElectronHistory => R y)
      (pole_reader_add A B)
  calc inner ℂ x (GaussUnitaryHistory.reader (A+B) y)
      = inner ℂ x (GaussUnitaryHistory.reader A y +
          GaussUnitaryHistory.reader B y) :=
        congrArg (fun v : ElectronHistory => inner ℂ x v) happ
    _ = inner ℂ x (GaussUnitaryHistory.reader A y) +
        inner ℂ x (GaussUnitaryHistory.reader B y) := inner_add_right x _ _

/-- Unit-modulus scalars drop out of the diagonal pairing. -/
private theorem pole_phase_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (A : E→L[ℂ]E) (v : E) :
    inner ℂ (ζ • v) (A (ζ • v)) = inner ℂ v (A v) := by
  have hmul : ζ * (starRingEnd ℂ) ζ = 1 := by
    simpa [hζ] using RCLike.mul_conj ζ
  rw [map_smul, inner_smul_right, inner_smul_left, ← mul_assoc, hmul, one_mul]

/-- The fixed-operator diagonal observer error between two unit states: the shared
background read cancels and the difference is `2‖A‖‖a-x‖`, generically. -/
private theorem pole_observer_diagonal_error {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E→L[ℂ]E) (a x b : E) (ha : ‖a‖ = 1) (hx : ‖x‖ = 1) :
    ‖(-inner ℂ a (A a)+inner ℂ b (A b))-(-inner ℂ x (A x)+inner ℂ b (A b))‖
      ≤ 2 * ‖A‖ * ‖a - x‖ := by
  have hsplit : inner ℂ a (A a) - inner ℂ x (A x) =
      inner ℂ (a - x) (A a) + inner ℂ x (A (a - x)) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  have hd : (-inner ℂ a (A a)+inner ℂ b (A b))-(-inner ℂ x (A x)+inner ℂ b (A b)) =
      -(inner ℂ a (A a) - inner ℂ x (A x)) := by
    abel
  rw [hd, norm_neg, hsplit]
  calc _ ≤ ‖inner ℂ (a - x) (A a)‖ + ‖inner ℂ x (A (a - x))‖ := norm_add_le _ _
    _ ≤ ‖a - x‖ * ‖A a‖ + ‖x‖ * ‖A (a - x)‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖a - x‖ * (‖A‖ * ‖a‖) + ‖x‖ * (‖A‖ * ‖a - x‖) :=
        add_le_add (mul_le_mul_of_nonneg_left (A.le_opNorm a) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (A.le_opNorm (a - x)) (norm_nonneg _))
    _ = _ := by rw [ha, hx]; ring

/-- The completed pole state reads the fixed event window operator through the
original `GaussUnitaryHistory.reader`, against the unchanged source background. -/
def physicalN3PoleWindowHistoryRead (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (k : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (reader force : Field289) : ℂ :=
  -inner ℂ (physicalN3PoleState event.momentum leg poles)
    (GaussUnitaryHistory.reader
      (physicalN3ResponseWindowOperator event k lambda T reader force)
      (physicalN3PoleState event.momentum leg poles))+
  inner ℂ (actualNoetherBackground event)
    (GaussUnitaryHistory.reader
      (physicalN3ResponseWindowOperator event k lambda T reader force)
      (actualNoetherBackground event))

/-- The completed approach state reads the same fixed event operator. -/
def physicalN3PoleApproachWindowHistoryRead (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (k : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (reader force : Field289) (m : ℕ) : ℂ :=
  -inner ℂ (physicalN3PoleApproachState event.momentum leg poles m)
    (GaussUnitaryHistory.reader
      (physicalN3ResponseWindowOperator event k lambda T reader force)
      (physicalN3PoleApproachState event.momentum leg poles m))+
  inner ℂ (actualNoetherBackground event)
    (GaussUnitaryHistory.reader
      (physicalN3ResponseWindowOperator event k lambda T reader force)
      (actualNoetherBackground event))

/-- The per-frame pole frame reads return through the original `sourceFilter` to the
completed history read. -/
theorem physical_n3_pole_window_source_return (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (k : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (reader force : Field289) :
    Tendsto (fun F => physicalN3PoleFrameRead event leg k lambda T reader force F
        (poles F))
      GaussUnitaryHistory.sourceFilter
      (𝓝 (physicalN3PoleWindowHistoryRead event leg poles k lambda T reader force)) := by
  unfold physicalN3PoleWindowHistoryRead physicalN3PoleFrameRead physicalN3PoleState
  rw [actualNoetherBackground]
  simp only [GaussUnitaryHistory.inclusion,GaussUnitaryHistory.reader,pole_embed_constant]
  exact pole_family_observer_return GaussUnitaryHistory.sourceFilter
    (physicalN3PoleFamily event.momentum leg poles)
    (SourceFamilyHilbert.constant GaussUnitaryHistory.sourceFilter
      (prepared (sourceProfile event.epsilon event.precision)))
    (SourceFamilyOperator.constant
      (physicalN3ResponseWindowOperator event k lambda T reader force))

/-- The actual frame approach reads at the generated approach energies return to the
completed approach-state read; phase invariance identifies the per-frame pairings. -/
theorem physical_n3_pole_approach_window_source_return (event : DressedEvent)
    (leg : CompositeLeg) (poles : N3SourceEnergyPoleSection event.momentum leg)
    (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289) (m : ℕ) :
    Tendsto (fun F => physicalN3ExternalEnergyFrameRead event leg k lambda T reader
        force F (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m))
      GaussUnitaryHistory.sourceFilter
      (𝓝 (physicalN3PoleApproachWindowHistoryRead event leg poles k lambda T reader
        force m)) := by
  unfold physicalN3PoleApproachWindowHistoryRead physicalN3ExternalEnergyFrameRead
    physicalN3PoleApproachState
  rw [actualNoetherBackground]
  simp only [GaussUnitaryHistory.inclusion,GaussUnitaryHistory.reader,pole_embed_constant]
  refine (pole_family_observer_return GaussUnitaryHistory.sourceFilter
    (physicalN3PoleApproachFamily event.momentum leg poles m)
    (SourceFamilyHilbert.constant GaussUnitaryHistory.sourceFilter
      (prepared (sourceProfile event.epsilon event.precision)))
    (SourceFamilyOperator.constant
      (physicalN3ResponseWindowOperator event k lambda T reader force))).congr' ?_
  apply Eventually.of_forall
  intro F
  have hunit : physicalN3PoleApproachUnit event.momentum F leg (poles F) m =
      physicalN3PolePhase event.momentum F leg (poles F) •
        actualElectronPhysicalUnit event.momentum F
          (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg :=
    physicalN3PoleApproachUnit.eq_def _ _ _ _ _
  have hph : inner ℂ (physicalN3PoleApproachUnit event.momentum F leg (poles F) m)
      (physicalN3ResponseWindowOperator event k lambda T reader force
        (physicalN3PoleApproachUnit event.momentum F leg (poles F) m)) =
    inner ℂ (actualElectronPhysicalUnit event.momentum F
        (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg)
      (physicalN3ResponseWindowOperator event k lambda T reader force
        (actualElectronPhysicalUnit event.momentum F
          (physicalN3PoleApproachEnergy event.momentum F leg (poles F) m) leg)) :=
    (congrArg (fun v : H => inner ℂ v
        (physicalN3ResponseWindowOperator event k lambda T reader force v)) hunit).trans
      (pole_phase_inner (physicalN3PolePhase event.momentum F leg (poles F))
        (physical_n3_pole_phase_norm event.momentum F leg (poles F)) _ _)
  show -inner ℂ (physicalN3PoleApproachUnit event.momentum F leg (poles F) m)
        (physicalN3ResponseWindowOperator event k lambda T reader force
          (physicalN3PoleApproachUnit event.momentum F leg (poles F) m))+
      inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (physicalN3ResponseWindowOperator event k lambda T reader force
          (prepared (sourceProfile event.epsilon event.precision))) = _
  exact congrArg (fun z : ℂ => -z +
    inner ℂ (prepared (sourceProfile event.epsilon event.precision))
      (physicalN3ResponseWindowOperator event k lambda T reader force
        (prepared (sourceProfile event.epsilon event.precision)))) hph

/-- The completed window difference is the fixed-operator diagonal error; the shared
prepared background cancels only in the difference and remains in both reads. -/
theorem physical_n3_pole_window_history_error (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (k : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (reader force : Field289) (m : ℕ) :
    ‖physicalN3PoleApproachWindowHistoryRead event leg poles k lambda T reader force m -
      physicalN3PoleWindowHistoryRead event leg poles k lambda T reader force‖
      ≤ 2 * ‖physicalN3ResponseWindowOperator event k lambda T reader force‖ *
        actualSoftBudget m := by
  have hRW : ‖GaussUnitaryHistory.reader
        (physicalN3ResponseWindowOperator event k lambda T reader force)‖
      ≤ ‖physicalN3ResponseWindowOperator event k lambda T reader force‖ :=
    pole_reader_bound GaussUnitaryHistory.sourceFilter _
  have herr := physical_n3_pole_state_error event.momentum leg poles m
  unfold physicalN3PoleApproachWindowHistoryRead physicalN3PoleWindowHistoryRead
  calc _ ≤ 2 * ‖GaussUnitaryHistory.reader
          (physicalN3ResponseWindowOperator event k lambda T reader force)‖ *
        ‖physicalN3PoleApproachState event.momentum leg poles m -
          physicalN3PoleState event.momentum leg poles‖ :=
        pole_observer_diagonal_error _ _ _ _
          (physical_n3_pole_approach_state_norm event.momentum leg poles m)
          (physical_n3_pole_state_norm event.momentum leg poles)
    _ ≤ 2 * ‖GaussUnitaryHistory.reader
          (physicalN3ResponseWindowOperator event k lambda T reader force)‖ *
        actualSoftBudget m :=
        mul_le_mul_of_nonneg_left herr
          (mul_nonneg (by norm_num) (norm_nonneg _))
    _ ≤ _ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRW (by norm_num))
          (actual_soft_budget_positive m).le

/-- The approach window history reads converge to the pole window history read. -/
theorem physical_n3_pole_window_history_return (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) (k : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (reader force : Field289) :
    Tendsto (fun m => physicalN3PoleApproachWindowHistoryRead event leg poles k lambda T
        reader force m) atTop
      (𝓝 (physicalN3PoleWindowHistoryRead event leg poles k lambda T reader force)) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon positive
  have hC : Tendsto (fun m =>
      2 * ‖physicalN3ResponseWindowOperator event k lambda T reader force‖ *
        actualSoftBudget m) atTop (𝓝 0) := by
    have := actual_soft_budget_tendsto.const_mul
      (2 * ‖physicalN3ResponseWindowOperator event k lambda T reader force‖)
    simpa using this
  exact (hC.eventually (eventually_lt_nhds positive)).mono (fun m small => by
    rw [dist_eq_norm]
    exact (physical_n3_pole_window_history_error event leg poles k lambda T reader
      force m).trans_lt small)

/-- The complete `Fin 289 × Fin 289` window square history return, coordinatewise. -/
theorem physical_n3_pole_window_history_square_return (event : DressedEvent)
    (leg : CompositeLeg) (poles : N3SourceEnergyPoleSection event.momentum leg)
    (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) :
    Tendsto (fun m => fun (i j : Fin 289) =>
        physicalN3PoleApproachWindowHistoryRead event leg poles k lambda T
          (PreparationVacuumActionFieldLift.fieldUnit i)
          (PreparationVacuumActionFieldLift.fieldUnit j) m)
      atTop (𝓝 (fun (i j : Fin 289) =>
        physicalN3PoleWindowHistoryRead event leg poles k lambda T
          (PreparationVacuumActionFieldLift.fieldUnit i)
          (PreparationVacuumActionFieldLift.fieldUnit j))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact physical_n3_pole_window_history_return event leg poles k lambda T
    (PreparationVacuumActionFieldLift.fieldUnit i)
    (PreparationVacuumActionFieldLift.fieldUnit j)

/-- The pole window history read splits as the same source rest-light channel plus the
same complete remainder channel, both on the completed pole state and the original
prepared background. -/
theorem physical_n3_pole_history_light_partition (event : DressedEvent)
    (leg : CompositeLeg) (poles : N3SourceEnergyPoleSection event.momentum leg)
    (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289) :
    physicalN3PoleWindowHistoryRead event leg poles k lambda T reader force =
      (-inner ℂ (physicalN3PoleState event.momentum leg poles)
        (GaussUnitaryHistory.reader
          (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader
            force) (physicalN3PoleState event.momentum leg poles))+
       inner ℂ (actualNoetherBackground event)
        (GaussUnitaryHistory.reader
          (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader
            force) (actualNoetherBackground event)))+
      (-inner ℂ (physicalN3PoleState event.momentum leg poles)
        (GaussUnitaryHistory.reader
          (sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T reader
            force) (physicalN3PoleState event.momentum leg poles))+
       inner ℂ (actualNoetherBackground event)
        (GaussUnitaryHistory.reader
          (sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T reader
            force) (actualNoetherBackground event))) := by
  have hsplit := actual_physical_n3_window_operator_source_rest_light_partition
    event k lambda T reader force
  unfold physicalN3PoleWindowHistoryRead
  calc _ = -inner ℂ (physicalN3PoleState event.momentum leg poles)
          (GaussUnitaryHistory.reader
            (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader
              force +
              sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T reader
                force)
            (physicalN3PoleState event.momentum leg poles))+
        inner ℂ (actualNoetherBackground event)
          (GaussUnitaryHistory.reader
            (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader
              force +
              sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T reader
                force)
            (actualNoetherBackground event)) :=
        congrArg (fun W : H→L[ℂ]H =>
          -inner ℂ (physicalN3PoleState event.momentum leg poles)
            (GaussUnitaryHistory.reader W
              (physicalN3PoleState event.momentum leg poles))+
          inner ℂ (actualNoetherBackground event)
            (GaussUnitaryHistory.reader W (actualNoetherBackground event))) hsplit
    _ = _ := by
        have h1 := pole_reader_inner_add
          (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader force)
          (sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T reader
            force) (physicalN3PoleState event.momentum leg poles)
          (physicalN3PoleState event.momentum leg poles)
        have h2 := pole_reader_inner_add
          (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader force)
          (sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T reader
            force) (actualNoetherBackground event) (actualNoetherBackground event)
        calc -inner ℂ (physicalN3PoleState event.momentum leg poles)
              (GaussUnitaryHistory.reader
                (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader
                  force +
                  sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T
                    reader force) (physicalN3PoleState event.momentum leg poles))+
            inner ℂ (actualNoetherBackground event)
              (GaussUnitaryHistory.reader
                (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader
                  force +
                  sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T
                    reader force) (actualNoetherBackground event))
          = -(inner ℂ (physicalN3PoleState event.momentum leg poles)
              (GaussUnitaryHistory.reader
                (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader
                  force) (physicalN3PoleState event.momentum leg poles))+
            inner ℂ (physicalN3PoleState event.momentum leg poles)
              (GaussUnitaryHistory.reader
                (sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T
                  reader force) (physicalN3PoleState event.momentum leg poles)))+
            inner ℂ (actualNoetherBackground event)
              (GaussUnitaryHistory.reader
                (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader
                  force +
                  sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T
                    reader force) (actualNoetherBackground event)) :=
            congrArg (fun u : ℂ => -u +
              inner ℂ (actualNoetherBackground event)
                (GaussUnitaryHistory.reader
                  (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader
                    force +
                    sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T
                      reader force) (actualNoetherBackground event))) h1
          _ = -(inner ℂ (physicalN3PoleState event.momentum leg poles)
              (GaussUnitaryHistory.reader
                (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader
                  force) (physicalN3PoleState event.momentum leg poles))+
            inner ℂ (physicalN3PoleState event.momentum leg poles)
              (GaussUnitaryHistory.reader
                (sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T
                  reader force) (physicalN3PoleState event.momentum leg poles)))+
            (inner ℂ (actualNoetherBackground event)
              (GaussUnitaryHistory.reader
                (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader
                  force) (actualNoetherBackground event))+
            inner ℂ (actualNoetherBackground event)
              (GaussUnitaryHistory.reader
                (sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T
                  reader force) (actualNoetherBackground event))) :=
            congrArg (fun v : ℂ =>
              -(inner ℂ (physicalN3PoleState event.momentum leg poles)
                (GaussUnitaryHistory.reader
                  (sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader
                    force) (physicalN3PoleState event.momentum leg poles))+
              inner ℂ (physicalN3PoleState event.momentum leg poles)
                (GaussUnitaryHistory.reader
                  (sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T
                    reader force) (physicalN3PoleState event.momentum leg poles)))+v) h2
          _ = _ := by ring

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
