import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Global
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.History
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery
open Collision Quantum Resource Propagation.Interface Propagation.Producer Load.Source Blocks
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def material : Material := Replenish.Runtime.readCurrent Replenish.Runtime.afterSecond
def origin : Live.State := material.quantum

theorem source_exact : material=Replenish.Account.output := Replenish.Runtime.actual_sequence.2.2

theorem origin_clock : origin.localClock=16*nativeClockStep := Replenish.Runtime.actual_clocks.2.2

theorem swap_product_nonnegative (rho tau : SystemMatrix Basis)
    (hRho : rho.PosSemidef) (hTau : tau.PosSemidef) :
    0 ≤ energy (swapOperator : JointMatrix Basis) (Matrix.kronecker rho tau) := by
  have trace := congrArg Matrix.trace (Collision.systemReduce_swap_tensor rho tau)
  rw [Collision.systemReduce_trace] at trace
  unfold energy
  rw [trace]
  exact QuadraticEnergy.positive_energy tau rho hTau hRho

theorem collision_swap_energy (rho tau : SystemMatrix Basis) (c s : ℝ)
    (circle : c^2+s^2=1) :
    energy (swapOperator : JointMatrix Basis) (jointNext rho tau c s) =
      energy (swapOperator : JointMatrix Basis) (Matrix.kronecker rho tau) := by
  let U : Matrix.unitaryGroup (Basis × Basis) ℂ := ⟨partialSwap c s,partialSwap_unitary c s circle⟩
  exact PreparationEnergy.commuting_energy _ _ U
    (((Commute.one_right _).smul_right (c : ℂ)).sub_right
      ((Commute.refl (swapOperator : JointMatrix Basis)).smul_right (Complex.I*(s : ℂ))))

theorem original_pair_swap_nonnegative :
    0 ≤ energy (swapOperator : JointMatrix Basis) Powered.Producer.sourceReceivedPair := by
  rw [Powered.Producer.sourceReceivedPair_eq_fieldTarget]
  have field := Work.Drive.fieldCycle_interactionEnergy Work.Drive.sourceFieldCycleCurrent
  change energy ((1 : ℂ) • (swapOperator : JointMatrix Basis)) Work.Drive.sourceFieldCycleTarget =
    energy ((1 : ℂ) • (swapOperator : JointMatrix Basis)) Work.Drive.sourceFieldCycleCurrent at field
  rw [one_smul] at field
  rw [field]
  change 0 ≤ energy (swapOperator : JointMatrix Basis)
    (Thermal.Dynamics.pairAdvance Thermal.Source.energyHamiltonian 1 (nativeClockStep : ℝ)
      Thermal.Producer.generatedJoint)
  have before := congrArg Complex.re
    (Thermal.Dynamics.pairAdvance_interactionEnergy Thermal.Source.energyHamiltonian
      Thermal.Source.energyHamiltonian_hermitian 1 (nativeClockStep : ℝ) Thermal.Producer.generatedJoint)
  change energy ((1 : ℂ) • (swapOperator : JointMatrix Basis)) _ =
    energy ((1 : ℂ) • (swapOperator : JointMatrix Basis)) _ at before
  rw [one_smul] at before
  rw [before,Thermal.Producer.generatedJoint,collision_swap_energy _ _ _ _ Thermal.Source.exchange_normalized]
  exact swap_product_nonnegative _ _ Thermal.Source.systemCurrent_posSemidef Thermal.Source.bathCurrent_posSemidef

theorem original_charged_work_lower :
    1 ≤ energy globalWork (Powered.Dynamics.chargedInput Powered.Producer.sourceReceivedPair) := by
  have lower := charged_work_lower Powered.Producer.sourceReceivedPair Powered.Producer.sourceParentState.positive
  have trace : Powered.Producer.sourceReceivedPair.trace=1 := Powered.Producer.sourceParentState.normalized
  rw [trace,Complex.one_re] at lower
  linarith only [lower,original_pair_swap_nonnegative]

def sixteenWord : Matrix.unitaryGroup PointerIndex ℂ :=
  Pointer.loadPulse (nativeClockStep : ℝ) * feedbackPulse (nativeClockStep : ℝ) *
    Extract.pointerPulse (nativeClockStep : ℝ) * Blocks.EnergyFrame.afterInstrumentEleven

theorem original_sixteen_from_instrument :
    origin.joint=conjugation sixteenWord sourceTarget := by
  have actualOrigin : origin=Replenish.Registered.execution := by
    have h := congrArg (fun current : Material => current.quantum) source_exact
    change origin=Replenish.Account.output.quantum at h
    exact h.trans Replenish.Account.output_quantum
  have entry : sourceEntry.quantum=Extract.next Weak.execution := Extract.Runtime.actual_sequence.2.1
  rw [actualOrigin,Replenish.Account.execution_joint,Replenish.origin_joint,entry,
    Extract.next_joint,Blocks.EnergyFrame.original_eleven_from_instrument,
    Environment.conjugation_comp,Environment.conjugation_comp,Environment.conjugation_comp]
  rfl

def idealPointerLoad (time : ℝ) : Matrix.unitaryGroup PointerIndex ℂ :=
  blockUnitary (FreeHistory.fullFree time) (freePhase time • FreeHistory.fullFree time)

def idealFeedback (time : ℝ) : Matrix.unitaryGroup PointerIndex ℂ :=
  blockUnitary (FreeHistory.fullFree time) (freePhase time • FreeHistory.idealSupply time)

theorem pointer_load_free_error (time : ℝ) :
    ‖(Pointer.loadPulse time : PointerJoint)-(idealPointerLoad time : PointerJoint)‖ ≤ |time| := by
  change ‖Matrix.fromBlocks (Current.loadPulse time : Current.FullJoint) 0 0
      ((freePhase time : ℂ) • (Current.loadPulse time : Current.FullJoint)) -
    Matrix.fromBlocks (FreeHistory.fullFree time : Current.FullJoint) 0 0
      ((freePhase time : ℂ) • (FreeHistory.fullFree time : Current.FullJoint))‖ ≤ _
  apply (Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.blocks_error _ _ _ _).trans
  apply max_le (FreeHistory.full_load_free_error time)
  rw [← smul_sub,norm_smul,CStarRing.norm_coe_unitary,one_mul]
  exact FreeHistory.full_load_free_error time

theorem feedback_full_swap_error :
    ‖(feedbackPulse (nativeClockStep : ℝ) : PointerJoint)-(idealFeedback (nativeClockStep : ℝ) : PointerJoint)‖ ≤
      (nativeClockStep : ℝ) := by
  change ‖Matrix.fromBlocks (Current.loadPulse (nativeClockStep : ℝ) : Current.FullJoint) 0 0
      ((freePhase (nativeClockStep : ℝ) : ℂ) • (Current.pulse (nativeClockStep : ℝ) : Current.FullJoint)) -
    Matrix.fromBlocks (FreeHistory.fullFree (nativeClockStep : ℝ) : Current.FullJoint) 0 0
      ((freePhase (nativeClockStep : ℝ) : ℂ) • (FreeHistory.idealSupply (nativeClockStep : ℝ) : Current.FullJoint))‖ ≤ _
  apply (Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.blocks_error _ _ _ _).trans
  apply max_le
  · have bound := FreeHistory.full_load_free_error (nativeClockStep : ℝ)
    have positive : 0 < (nativeClockStep : ℝ) := by exact_mod_cast nativeClockStep_positive
    rw [abs_of_pos positive] at bound
    exact bound
  · rw [← smul_sub,norm_smul,CStarRing.norm_coe_unitary,one_mul]
    exact FreeHistory.supply_clock_error_sharp

theorem weak_pointer_free_error (time : ℝ) :
    ‖(Weak.pointerPulse time : PointerJoint)-(idealPointerLoad time : PointerJoint)‖ ≤ |time| := by
  change ‖Matrix.fromBlocks (Current.loadPulse time : Current.FullJoint) 0 0
      ((freePhase time : ℂ) • (Weak.fullPulse time : Current.FullJoint)) -
    Matrix.fromBlocks (FreeHistory.fullFree time : Current.FullJoint) 0 0
      ((freePhase time : ℂ) • (FreeHistory.fullFree time : Current.FullJoint))‖ ≤ _
  apply (Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.blocks_error _ _ _ _).trans
  apply max_le (FreeHistory.full_load_free_error time)
  rw [← smul_sub,norm_smul,CStarRing.norm_coe_unitary,one_mul]
  exact FreeHistory.weak_free_error time

def idealSixteenWord : Matrix.unitaryGroup PointerIndex ℂ :=
  idealPointerLoad (nativeClockStep : ℝ) * idealFeedback (nativeClockStep : ℝ) *
    Extract.pointerPulse (nativeClockStep : ℝ) *
    (idealPointerLoad (nativeClockStep : ℝ) * idealPointerLoad (nativeClockStep : ℝ) *
      (idealPointerLoad (nativeClockStep : ℝ) * idealFeedback (nativeClockStep : ℝ) *
        idealFeedback (nativeClockStep : ℝ)))

theorem sixteen_word_error :
    ‖(sixteenWord : PointerJoint)-(idealSixteenWord : PointerJoint)‖ ≤ 7*(nativeClockStep : ℝ) := by
  let q : ℝ := nativeClockStep
  let L := Pointer.loadPulse q
  let F := feedbackPulse q
  let W := Weak.pointerPulse q
  let X := Extract.pointerPulse q
  let A := idealPointerLoad q
  let B := idealFeedback q
  have positive : 0 < (nativeClockStep : ℝ) := by exact_mod_cast nativeClockStep_positive
  have leL : ‖(L : PointerJoint)-(A : PointerJoint)‖ ≤ q := by
    simpa only [abs_of_pos positive] using pointer_load_free_error (nativeClockStep : ℝ)
  have leF : ‖(F : PointerJoint)-(B : PointerJoint)‖ ≤ q := feedback_full_swap_error
  have leW : ‖(W : PointerJoint)-(A : PointerJoint)‖ ≤ q := by
    simpa only [abs_of_pos positive] using weak_pointer_free_error (nativeClockStep : ℝ)
  have leX : ‖(X : PointerJoint)-(X : PointerJoint)‖ ≤ 0 := by simp
  have lf := (FreeHistory.unitary_product_distance L F A B).trans (add_le_add leL leF)
  have nine := (FreeHistory.unitary_product_distance (L*F) F (A*B) B).trans (add_le_add lf leF)
  have lw := (FreeHistory.unitary_product_distance L W A A).trans (add_le_add leL leW)
  have eleven := (FreeHistory.unitary_product_distance (L*W) (L*F*F) (A*A) (A*B*B)).trans (add_le_add lw nine)
  have tail := (FreeHistory.unitary_product_distance (L*F) X (A*B) X).trans (add_le_add lf leX)
  have finalBound := (FreeHistory.unitary_product_distance (L*F*X) (L*W*(L*F*F))
    (A*B*X) (A*A*(A*B*B))).trans (add_le_add tail eleven)
  change ‖(sixteenWord : PointerJoint)-(idealSixteenWord : PointerJoint)‖ ≤
    (q+q+0)+((q+q)+(q+q+q)) at finalBound
  change ‖(sixteenWord : PointerJoint)-(idealSixteenWord : PointerJoint)‖ ≤ 7*q
  linarith only [finalBound]

def preparationBase : PointerJoint :=
  prepared (Incidence.receivedJoint Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.preparedBody Reservoir.Source.donor)

def preparationWord : Matrix.unitaryGroup Current.FullIndex ℂ :=
  Current.pulse (nativeClockStep : ℝ) *
    Incidence.bodyLift Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.receivedWord

def idealPreparationWord : Matrix.unitaryGroup Current.FullIndex ℂ :=
  FreeHistory.idealSupply (nativeClockStep : ℝ) * Incidence.bodyLift FreeHistory.freeReceivedWord

def completeWord : Matrix.unitaryGroup PointerIndex ℂ :=
  sixteenWord*sourceUnitary*blockUnitary preparationWord preparationWord

def idealCompleteWord : Matrix.unitaryGroup PointerIndex ℂ :=
  idealSixteenWord*sourceUnitary*blockUnitary idealPreparationWord idealPreparationWord

theorem original_initial_from_base :
    sourceInitial=conjugation (blockUnitary preparationWord preparationWord) preparationBase := by
  change prepared (Current.supplyNext Current.initial).joint=_
  rw [Current.supplyNext_joint,Current.initial_receives_actual,
    Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.original_received_from_preparation,
    ← Incidence.bodyLift_received,Environment.conjugation_comp,Environment.prepared_conjugation]
  rfl

theorem original_complete_word : origin.joint=conjugation completeWord preparationBase := by
  rw [original_sixteen_from_instrument,sourceTarget_generated,original_initial_from_base,
    Environment.conjugation_comp,Environment.conjugation_comp]
  rfl

theorem preparation_body_error :
    ‖(Incidence.bodyLift Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.receivedWord : Current.FullJoint) -
      (Incidence.bodyLift FreeHistory.freeReceivedWord : Current.FullJoint)‖ ≤ (nativeClockStep : ℝ) := by
  have split :
      (Incidence.bodyLift Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.receivedWord : Current.FullJoint) -
        (Incidence.bodyLift FreeHistory.freeReceivedWord : Current.FullJoint) =
      Blocks.EnergyFrame.bodyRegroup
        ((Load.Quantum.localUnitary Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.receivedWord
          (1 : Matrix.unitaryGroup PairController ℂ) :
            Matrix ((PairController × Fin 2) × PairController) ((PairController × Fin 2) × PairController) ℂ) -
          (Load.Quantum.localUnitary FreeHistory.freeReceivedWord
          (1 : Matrix.unitaryGroup PairController ℂ) :
            Matrix ((PairController × Fin 2) × PairController) ((PairController × Fin 2) × PairController) ℂ)) := rfl
  rw [split,StarAlgEquiv.norm_map]
  exact (FreeHistory.local_left_error _ _ _).trans FreeHistory.original_received_word_error

theorem preparation_word_error :
    ‖(preparationWord : Current.FullJoint)-(idealPreparationWord : Current.FullJoint)‖ ≤ 2*(nativeClockStep : ℝ) := by
  have bound := (FreeHistory.unitary_product_distance
    (Current.pulse (nativeClockStep : ℝ))
    (Incidence.bodyLift Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.receivedWord)
    (FreeHistory.idealSupply (nativeClockStep : ℝ)) (Incidence.bodyLift FreeHistory.freeReceivedWord)).trans
      (add_le_add FreeHistory.supply_clock_error_sharp preparation_body_error)
  change ‖(preparationWord : Current.FullJoint)-(idealPreparationWord : Current.FullJoint)‖ ≤
    (nativeClockStep : ℝ)+(nativeClockStep : ℝ) at bound
  linarith only [bound]

theorem preparation_pointer_error :
    ‖(blockUnitary preparationWord preparationWord : PointerJoint) -
      (blockUnitary idealPreparationWord idealPreparationWord : PointerJoint)‖ ≤ 2*(nativeClockStep : ℝ) := by
  have bound := Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.blocks_error
    (preparationWord : Current.FullJoint) preparationWord
    (idealPreparationWord : Current.FullJoint) idealPreparationWord
  rw [max_self] at bound
  exact bound.trans preparation_word_error

theorem complete_word_error :
    ‖(completeWord : PointerJoint)-(idealCompleteWord : PointerJoint)‖ ≤ 9*(nativeClockStep : ℝ) := by
  have fixed : ‖(sourceUnitary : PointerJoint)-(sourceUnitary : PointerJoint)‖ ≤ 0 := by simp
  have prefixBound := (FreeHistory.unitary_product_distance sixteenWord sourceUnitary idealSixteenWord sourceUnitary).trans
    (add_le_add sixteen_word_error fixed)
  have finalBound := (FreeHistory.unitary_product_distance (sixteenWord*sourceUnitary)
    (blockUnitary preparationWord preparationWord) (idealSixteenWord*sourceUnitary)
    (blockUnitary idealPreparationWord idealPreparationWord)).trans
      (add_le_add prefixBound preparation_pointer_error)
  change ‖(completeWord : PointerJoint)-(idealCompleteWord : PointerJoint)‖ ≤
    (7*(nativeClockStep : ℝ)+0)+2*(nativeClockStep : ℝ) at finalBound
  linarith only [finalBound]

theorem preparation_base_positive : preparationBase.PosSemidef :=
  prepared_positive _ (Incidence.receivedJoint_positive _ _
    ((Powered.Dynamics.chargedInput_positive _ Powered.Producer.sourceParentState.positive).kronecker environmentState_positive)
    Reservoir.Source.donor_positive)

theorem preparation_base_trace : preparationBase.trace=1 := by
  have pairTrace : Powered.Producer.sourceReceivedPair.trace=1 := Powered.Producer.sourceParentState.normalized
  have chargedTrace := Powered.Dynamics.chargedInput_trace Powered.Producer.sourceReceivedPair pairTrace
  rw [preparationBase,prepared_trace,Incidence.receivedJoint_trace,Reservoir.Source.donor_trace,mul_one,
    Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.preparedBody,Matrix.kronecker,Matrix.trace_kronecker,
    chargedTrace,environmentState_trace,mul_one]

def idealSixteen : PointerJoint := conjugation idealCompleteWord preparationBase

theorem complete_observer_error (O : PointerJoint) :
    |energy O origin.joint-energy O idealSixteen| ≤ 18*‖O‖*(nativeClockStep : ℝ) := by
  have bound := weighted_observable_error O preparationBase preparation_base_positive completeWord idealCompleteWord
  rw [preparation_base_trace,Complex.one_re,mul_one] at bound
  rw [original_complete_word]
  apply bound.trans
  calc
    _ ≤ 2*‖O‖*(9*(nativeClockStep : ℝ)) :=
      mul_le_mul_of_nonneg_left complete_word_error (mul_nonneg (by norm_num) (norm_nonneg O))
    _ = _ := by ring

theorem free_pc_comp (s t : ℝ) (rho : Matrix PairController PairController ℂ) :
    conjugation (Native.freePCUnitary s) (conjugation (Native.freePCUnitary t) rho)=
      conjugation (Native.freePCUnitary (s+t)) rho := by
  have times : Native.freePCUnitary (s+t)=Native.freePCUnitary s*Native.freePCUnitary t :=
    Powered.Dynamics.flowUnitary_add _ _ _ _ _ s t
  rw [Environment.conjugation_comp,← times]

theorem ideal_load_right (time : ℝ) (rho : PointerJoint) :
    (conjugation (idealPointerLoad time) rho).toBlocks₂₂=
      conjugation (FreeHistory.fullFree time) rho.toBlocks₂₂ := by
  rw [idealPointerLoad,controlled_block_right]
  exact unitPhase_conjugation _ _ _

theorem ideal_feedback_right (time : ℝ) (rho : PointerJoint) :
    (conjugation (idealFeedback time) rho).toBlocks₂₂=
      conjugation (FreeHistory.idealSupply time) rho.toBlocks₂₂ := by
  rw [idealFeedback,controlled_block_right]
  exact unitPhase_conjugation _ _ _

theorem extraction_right (time : ℝ) (rho : PointerJoint) :
    (conjugation (Extract.pointerPulse time) rho).toBlocks₂₂=
      conjugation (Extract.fullPulse time) rho.toBlocks₂₂ := by
  rw [Extract.pointerPulse,controlled_block_right]

theorem ideal_post_right_pc (rho : PointerJoint) :
    Resource.pcMatrixOf (conjugation idealSixteenWord rho).toBlocks₂₂=
      conjugation (Native.freePCUnitary (7*(nativeClockStep : ℝ))) (Resource.donorMatrixOf rho.toBlocks₂₂) := by
  simp only [idealSixteenWord,← Environment.conjugation_comp,ideal_load_right,ideal_feedback_right,extraction_right,
    FreeHistory.full_free_pc,FreeHistory.ideal_supply_pc,Extract.full_donor,FreeHistory.full_free_donor,
    FreeHistory.ideal_supply_donor,free_pc_comp]
  congr 2
  ring

def sourceBodyEffect : LoadedJoint := Measurement.sourceMeasurementEffect Load.Source.loadTotalHamiltonian
def retainedPC : Matrix PairController PairController ℂ :=
  conjugation (Native.freePCUnitary (nativeClockStep : ℝ))
    (conjugation FreeHistory.freeReceivedPC (Powered.Dynamics.chargedInput Powered.Producer.sourceReceivedPair))
def measurementInput : LoadedJoint :=
  conjugation (FreeHistory.freeLoad (nativeClockStep : ℝ))
    (Matrix.kronecker Reservoir.Source.donor (conjugation FreeHistory.freeReceivedEnvironment environmentState))
def measuredRight : LoadedJoint := complementRoot sourceBodyEffect*measurementInput*complementRoot sourceBodyEffect
def idealInstrument : PointerJoint :=
  conjugation sourceUnitary (conjugation (blockUnitary idealPreparationWord idealPreparationWord) preparationBase)
def recoveredPCPhase : Matrix.unitaryGroup PairController ℂ :=
  Native.freePCUnitary (8*(nativeClockStep : ℝ))*FreeHistory.freeReceivedPC
def idealMass : ℝ := measuredRight.trace.re

theorem ideal_preparation_product :
    conjugation idealPreparationWord
      (Incidence.receivedJoint Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.preparedBody Reservoir.Source.donor)=
        Incidence.receivedJoint measurementInput retainedPC := by
  rw [idealPreparationWord,← Environment.conjugation_comp,Incidence.bodyLift_received,
    FreeHistory.free_received_product,FreeHistory.ideal_supply_product]
  rfl

theorem ideal_instrument_right :
    idealInstrument.toBlocks₂₂=Incidence.receivedJoint measuredRight retainedPC := by
  rw [idealInstrument,preparationBase,← Environment.prepared_conjugation,ideal_preparation_product]
  have lawful := Measurement.sourceMeasurement_lawful Load.Source.loadTotalHamiltonian Load.Source.loadTotalHamiltonian_hermitian
  have result := FreeHistory.exact_instrument_conjugation_right sourceBodyEffect measurementInput retainedPC lawful.1 lawful.2
  simpa only [sourceUnitary,sourceEffect,sourceBodyEffect,measuredRight] using result


theorem ideal_sixteen_from_instrument :
    idealSixteen=conjugation idealSixteenWord idealInstrument := by
  rw [idealInstrument,Environment.conjugation_comp,Environment.conjugation_comp]
  rfl

theorem ideal_right_pc :
    Resource.pcMatrixOf idealSixteen.toBlocks₂₂=
      measuredRight.trace • conjugation recoveredPCPhase
        (Powered.Dynamics.chargedInput Powered.Producer.sourceReceivedPair) := by
  have donorRead : Resource.donorMatrixOf (Incidence.receivedJoint measuredRight retainedPC)=
      measuredRight.trace • retainedPC := FreeHistory.received_product_donor _ _
  rw [ideal_sixteen_from_instrument,ideal_post_right_pc,ideal_instrument_right,
    donorRead,map_smul,retainedPC,free_pc_comp]
  have time : 7*(nativeClockStep : ℝ)+(nativeClockStep : ℝ)=8*(nativeClockStep : ℝ) := by ring
  rw [time,Environment.conjugation_comp]
  rfl

theorem measured_right_positive : measuredRight.PosSemidef := by
  have body : measurementInput.PosSemidef :=
    conjugation_posSemidef _ _ (Reservoir.Source.donor_positive.kronecker
      (conjugation_posSemidef _ _ environmentState_positive))
  have positive := body.mul_mul_conjTranspose_same (complementRoot sourceBodyEffect)
  rw [(complementRoot_positive sourceBodyEffect).isHermitian.eq] at positive
  exact positive

theorem ideal_mass_nonnegative : 0 ≤ idealMass := (Complex.nonneg_iff.mp measured_right_positive.trace_nonneg).1

theorem measured_trace_real : measuredRight.trace=(idealMass : ℂ) := by
  unfold idealMass
  exact FreeHistory.positive_trace_real measuredRight measured_right_positive


theorem charged_trace : (Powered.Dynamics.chargedInput Powered.Producer.sourceReceivedPair).trace=1 :=
  Powered.Dynamics.chargedInput_trace _ Powered.Producer.sourceParentState.normalized

private theorem pointer_mass_of_reduced {ι κ : Type*} [Fintype ι] [Fintype κ]
    (rho : Matrix (((ι × ι) × κ) ⊕ ((ι × ι) × κ)) (((ι × ι) × κ) ⊕ ((ι × ι) × κ)) ℂ)
    (p : ℂ) (tau : Matrix ι ι ℂ)
    (reduced : Collision.systemReduce (Powered.Dynamics.systemReduce rho.toBlocks₂₂)=p • tau)
    (trace : tau.trace=1) : oneRead rho=p.re :=
  congrArg Complex.re (FreeHistory.pc_mass_of_reduced rho.toBlocks₂₂ p tau reduced trace)

theorem ideal_mass_read : oneRead idealSixteen=idealMass := by
  have trace : (conjugation recoveredPCPhase (Powered.Dynamics.chargedInput Powered.Producer.sourceReceivedPair)).trace=1 :=
    (conjugation_trace _ _).trans charged_trace
  unfold idealMass
  exact pointer_mass_of_reduced idealSixteen measuredRight.trace
    (conjugation recoveredPCPhase (Powered.Dynamics.chargedInput Powered.Producer.sourceReceivedPair)) ideal_right_pc trace


theorem recovered_phase_energy (rho : Matrix PairController PairController ℂ) :
    energy Powered.Producer.poweredTotalHamiltonian (conjugation recoveredPCPhase rho)=
      energy Powered.Producer.poweredTotalHamiltonian rho := by
  rw [recoveredPCPhase,← Environment.conjugation_comp,Native.freePC_energy,FreeHistory.free_received_pc_energy]

theorem ideal_right_work_lower :
    idealMass ≤ energy (transportedWork recoveredPCPhase) (Resource.pcMatrixOf idealSixteen.toBlocks₂₂) := by
  have scaling (rho : Matrix PairController PairController ℂ) :
      measuredRight.trace • rho=idealMass • rho := by
    rw [measured_trace_real]
    ext i j
    simp [Complex.real_smul]
  rw [ideal_right_pc,scaling]
  have read : energy (transportedWork recoveredPCPhase)
      (idealMass • conjugation recoveredPCPhase (Powered.Dynamics.chargedInput Powered.Producer.sourceReceivedPair)) =
      idealMass * energy (transportedWork recoveredPCPhase)
        (conjugation recoveredPCPhase (Powered.Dynamics.chargedInput Powered.Producer.sourceReceivedPair)) := by
    simp only [energy,Matrix.mul_smul,Matrix.trace_smul,Complex.real_smul,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [read,transported_reference_read]
  nlinarith only [ideal_mass_nonnegative,original_charged_work_lower]

def rightPCWork : PointerJoint :=
  Replenish.Readout.rightBlock (Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.pcLift
    (transportedWork recoveredPCPhase))
def rightMassObservable : PointerJoint := Replenish.Readout.rightBlock (1 : Current.FullJoint)

theorem right_pc_work_norm : ‖rightPCWork‖ ≤ 4 :=
  (Replenish.Readout.right_norm _).trans
    ((Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.pc_lift_norm _).trans (transported_work_norm _))

theorem right_pc_work_read (rho : PointerJoint) :
    energy rightPCWork rho=energy (transportedWork recoveredPCPhase) (Resource.pcMatrixOf rho.toBlocks₂₂) := by
  rw [rightPCWork,Replenish.Physical.right_energy,Blocks.EnergyFrame.Inverse.Scaled.Finite.Population.pc_lift_energy]

theorem right_mass_norm : ‖rightMassObservable‖ ≤ 1 := by
  exact (Replenish.Readout.right_norm _).trans (by simp)

theorem right_mass_read (rho : PointerJoint) : energy rightMassObservable rho=oneRead rho :=
  FreeHistory.right_identity_read rho


theorem actual_pointer_mass : (1/2 : ℝ) < oneRead origin.joint := by
  have actualOrigin : origin=Replenish.Registered.execution := by
    have h := congrArg (fun current : Material => current.quantum) source_exact
    change origin=Replenish.Account.output.quantum at h
    exact h.trans Replenish.Account.output_quantum
  rw [actualOrigin,Replenish.Account.execution_memory,Replenish.origin_joint]
  exact current_pointer_population

theorem ideal_mass_lower : (1/2 : ℝ)-18*(nativeClockStep : ℝ) < idealMass := by
  have bound := complete_observer_error rightMassObservable
  rw [right_mass_read,right_mass_read,ideal_mass_read] at bound
  have upper : 18*‖rightMassObservable‖*(nativeClockStep : ℝ) ≤ 18*(nativeClockStep : ℝ) := by
    have positive : 0 ≤ (nativeClockStep : ℝ) := by exact_mod_cast nativeClockStep_positive.le
    nlinarith only [right_mass_norm,positive]
  have error := (abs_le.mp (bound.trans upper)).2
  linarith only [error,actual_pointer_mass]

theorem actual_right_pc_work_lower :
    (1/2 : ℝ)-90*(nativeClockStep : ℝ) <
      energy (transportedWork recoveredPCPhase) (Resource.pcMatrixOf origin.joint.toBlocks₂₂) := by
  have bound := complete_observer_error rightPCWork
  rw [right_pc_work_read,right_pc_work_read] at bound
  have upper : 18*‖rightPCWork‖*(nativeClockStep : ℝ) ≤ 72*(nativeClockStep : ℝ) := by
    have positive : 0 ≤ (nativeClockStep : ℝ) := by exact_mod_cast nativeClockStep_positive.le
    nlinarith only [right_pc_work_norm,positive]
  have error := (abs_le.mp (bound.trans upper)).1
  linarith only [error,ideal_mass_lower,ideal_right_work_lower]

theorem actual_right_pc_work_positive :
    (46/100 : ℝ) < energy (transportedWork recoveredPCPhase) (Resource.pcMatrixOf origin.joint.toBlocks₂₂) := by
  have clock : (46/100 : ℝ) < (1/2 : ℝ)-90*(nativeClockStep : ℝ) := by
    rw [nativeClockStep_exact]
    norm_num
  exact clock.trans actual_right_pc_work_lower

def recoveredPCControl : Matrix.unitaryGroup PairController ℂ := transportedControl recoveredPCPhase
def recoveredBodyControl : Matrix.unitaryGroup Current.FullIndex ℂ :=
  Load.Quantum.localUnitary (Quantum.localUnitary recoveredPCControl 1) 1
def recoveredPointerControl : Matrix.unitaryGroup PointerIndex ℂ :=
  blockUnitary 1 recoveredBodyControl

def recoveredNext (current : Live.State) : Live.State :=
  ⟨current.localClock+nativeClockStep,recoveredPointerControl*current.action⟩

theorem recovered_next_joint (current : Live.State) :
    (recoveredNext current).joint=conjugation recoveredPointerControl current.joint :=
  (Environment.conjugation_comp _ current.action sourceInitial).symm

theorem recovered_clock : (recoveredNext origin).localClock=17*nativeClockStep := by
  change origin.localClock+nativeClockStep=_
  rw [origin_clock]
  ring

theorem recovered_body_pc (rho : Current.FullJoint) :
    Resource.pcMatrixOf (conjugation recoveredBodyControl rho)=
      conjugation recoveredPCControl (Resource.pcMatrixOf rho) := by
  unfold Resource.pcMatrixOf
  have outer := Load.Quantum.systemReduce_local_conjugation
    (Quantum.localUnitary recoveredPCControl 1) (1 : Matrix.unitaryGroup (Fin 2) ℂ) rho
  change Powered.Dynamics.systemReduce (conjugation recoveredBodyControl rho)=_ at outer
  rw [outer]
  exact Quantum.systemReduce_local_conjugation _ _ _

theorem recovered_body_read (rho : PointerJoint) :
    bodyRead (conjugation recoveredPointerControl rho)=
      rho.toBlocks₁₁+conjugation recoveredBodyControl rho.toBlocks₂₂ := by
  rw [bodyRead,recoveredPointerControl,controlled_block_left,controlled_block_right]
  simp only [conjugation_apply,Submonoid.coe_one,star_one,Matrix.one_mul,Matrix.mul_one]

theorem recovered_pc_work (rho : PointerJoint) :
    pcEnergyOf (bodyRead rho)-pcEnergyOf (bodyRead (conjugation recoveredPointerControl rho))=
      energy (transportedWork recoveredPCPhase) (Resource.pcMatrixOf rho.toBlocks₂₂) := by
  rw [recovered_body_read,bodyRead,pcEnergyOf_add,pcEnergyOf_add]
  have cancel (a b c : ℝ) : a+b-(a+c)=b-c := by ring
  rw [cancel]
  unfold pcEnergyOf
  rw [recovered_body_pc]
  exact transported_work_readout recoveredPCPhase recovered_phase_energy _

theorem recovered_actual_pc_gain :
    (46/100 : ℝ) < pcEnergyOf (bodyRead origin.joint) -
      pcEnergyOf (bodyRead (recoveredNext origin).joint) := by
  rw [recovered_next_joint,recovered_pc_work]
  exact actual_right_pc_work_positive

def idealElevenPrefix : Matrix.unitaryGroup PointerIndex ℂ :=
  idealPointerLoad (nativeClockStep : ℝ)*idealPointerLoad (nativeClockStep : ℝ)*
    (idealPointerLoad (nativeClockStep : ℝ)*idealFeedback (nativeClockStep : ℝ)*idealFeedback (nativeClockStep : ℝ))

theorem ideal_prefix_right (rho : PointerJoint) :
    (conjugation idealElevenPrefix rho).toBlocks₂₂=
      conjugation (FreeHistory.fullFree (5*(nativeClockStep : ℝ))) rho.toBlocks₂₂ := by
  simp only [idealElevenPrefix,← Environment.conjugation_comp,ideal_load_right,ideal_feedback_right]
  rw [FreeHistory.ideal_supply_twice]
  simp only [Environment.conjugation_comp,← FreeHistory.full_free_add]
  exact congrArg (fun t : ℝ => conjugation (FreeHistory.fullFree t) rho.toBlocks₂₂) (by ring)

def postExtractionBody : LoadedJoint :=
  conjugation (Load.Quantum.localUnitary (Extract.pcPulse (nativeClockStep : ℝ)) (1 : Matrix.unitaryGroup (Fin 2) ℂ))
    (conjugation (FreeHistory.freeLoad (5*(nativeClockStep : ℝ))) measuredRight)
def postExtractionDonor : Matrix PairController PairController ℂ :=
  conjugation (Native.freePCUnitary (5*(nativeClockStep : ℝ))) retainedPC
def idealEnvironment : Matrix (Fin 2) (Fin 2) ℂ :=
  conjugation (Load.Recovery.Control.environmentUnitary (2*(nativeClockStep : ℝ)))
    (Powered.Dynamics.controllerReduce postExtractionBody)

theorem ideal_sixteen_right_state :
    idealSixteen.toBlocks₂₂=
      conjugation (FreeHistory.fullFree (nativeClockStep : ℝ))
        (conjugation (FreeHistory.idealSupply (nativeClockStep : ℝ))
          (Incidence.receivedJoint postExtractionBody postExtractionDonor)) := by
  have word : idealSixteenWord=idealPointerLoad (nativeClockStep : ℝ)*idealFeedback (nativeClockStep : ℝ)*
      Extract.pointerPulse (nativeClockStep : ℝ)*idealElevenPrefix := rfl
  rw [ideal_sixteen_from_instrument,word]
  simp only [← Environment.conjugation_comp,ideal_load_right,ideal_feedback_right,extraction_right,
    ideal_prefix_right,ideal_instrument_right]
  rw [FreeHistory.full_free_received]
  have extraction :
      conjugation (Extract.fullPulse (nativeClockStep : ℝ))
        (Incidence.receivedJoint
          (conjugation (FreeHistory.freeLoad (5*(nativeClockStep : ℝ))) measuredRight)
          (conjugation (Native.freePCUnitary (5*(nativeClockStep : ℝ))) retainedPC)) =
        Incidence.receivedJoint postExtractionBody postExtractionDonor :=
    FreeHistory.pc_lift_received _ _ _
  rw [extraction]

theorem ideal_right_body_product :
    Incidence.bodyRead idealSixteen.toBlocks₂₂=
      Matrix.kronecker
        (conjugation recoveredPCPhase (Powered.Dynamics.chargedInput Powered.Producer.sourceReceivedPair))
        idealEnvironment := by
  rw [ideal_sixteen_right_state,FreeHistory.full_free_body_read,FreeHistory.ideal_supply_body_read]
  have tensor (A : Matrix PairController PairController ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
      conjugation (FreeHistory.freeLoad (nativeClockStep : ℝ)) (Matrix.kronecker A B)=
        Matrix.kronecker (conjugation (Native.freePCUnitary (nativeClockStep : ℝ)) A)
          (conjugation (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ)) B) :=
    Load.Quantum.localConjugation_tensor _ _ _ _
  rw [tensor]
  have pc :
      conjugation (Native.freePCUnitary (nativeClockStep : ℝ))
        (conjugation (Native.freePCUnitary (nativeClockStep : ℝ)) postExtractionDonor)=
      conjugation recoveredPCPhase (Powered.Dynamics.chargedInput Powered.Producer.sourceReceivedPair) := by
    rw [postExtractionDonor,retainedPC]
    simp only [free_pc_comp]
    have time : (nativeClockStep : ℝ)+((nativeClockStep : ℝ)+(5*(nativeClockStep : ℝ)+(nativeClockStep : ℝ)))=
        8*(nativeClockStep : ℝ) := by ring
    rw [time,Environment.conjugation_comp]
    rfl
  have env :
      conjugation (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ))
        (conjugation (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ))
          (Powered.Dynamics.controllerReduce postExtractionBody))=idealEnvironment := by
    rw [Environment.conjugation_comp,← Load.Recovery.Control.environmentUnitary_add,
      show (nativeClockStep : ℝ)+(nativeClockStep : ℝ)=2*(nativeClockStep : ℝ) by ring]
    rfl
  rw [pc,env]

theorem ideal_environment_positive : idealEnvironment.PosSemidef := by
  have body : postExtractionBody.PosSemidef :=
    conjugation_posSemidef _ _ (conjugation_posSemidef _ _ measured_right_positive)
  exact conjugation_posSemidef _ _ (Powered.Dynamics.controllerReduce_posSemidef _ body)

theorem ideal_environment_trace : idealEnvironment.trace=measuredRight.trace := by
  rw [idealEnvironment,conjugation_trace,Powered.Dynamics.controllerReduce_trace,
    postExtractionBody,conjugation_trace,conjugation_trace]

def chargedSeed : Matrix PairController PairController ℂ :=
  Powered.Dynamics.chargedInput Powered.Producer.sourceReceivedPair
def boundaryReferenceEnv : Matrix (Fin 2) (Fin 2) ℂ :=
  conjugation (star (Load.Recovery.Control.environmentUnitary (8*(nativeClockStep : ℝ)))) idealEnvironment
def boundarySeed (pc : Matrix PairController PairController ℂ) : LoadedJoint :=
  Matrix.kronecker (conjugation FreeHistory.freeReceivedPC pc) boundaryReferenceEnv

theorem boundary_reference_env_positive : boundaryReferenceEnv.PosSemidef :=
  conjugation_posSemidef _ _ ideal_environment_positive

theorem boundary_seed_positive (pc : Matrix PairController PairController ℂ) (positive : pc.PosSemidef) :
    (boundarySeed pc).PosSemidef :=
  (conjugation_posSemidef _ _ positive).kronecker boundary_reference_env_positive

theorem boundary_seed_trace (pc : Matrix PairController PairController ℂ) (trace : pc.trace=1) :
    (boundarySeed pc).trace=measuredRight.trace := by
  rw [boundarySeed,Matrix.kronecker,Matrix.trace_kronecker,conjugation_trace,trace,one_mul,
    boundaryReferenceEnv,conjugation_trace,ideal_environment_trace]

theorem boundary_seed_free (pc : Matrix PairController PairController ℂ) :
    conjugation (FreeHistory.freeLoad (8*(nativeClockStep : ℝ))) (boundarySeed pc)=
      Matrix.kronecker (conjugation recoveredPCPhase pc) idealEnvironment := by
  rw [boundarySeed]
  change Load.Quantum.localConjugation (Native.freePCUnitary (8*(nativeClockStep : ℝ)))
    (Load.Recovery.Control.environmentUnitary (8*(nativeClockStep : ℝ)))
      (Matrix.kronecker (conjugation FreeHistory.freeReceivedPC pc) boundaryReferenceEnv)=_
  rw [Load.Quantum.localConjugation_tensor,Environment.conjugation_comp]
  have inverse :
      conjugation (Load.Recovery.Control.environmentUnitary (8*(nativeClockStep : ℝ))) boundaryReferenceEnv=idealEnvironment := by
    change Unitary.conjStarAlgAut ℂ _ (Load.Recovery.Control.environmentUnitary (8*(nativeClockStep : ℝ)))
      (Unitary.conjStarAlgAut ℂ _ (star (Load.Recovery.Control.environmentUnitary (8*(nativeClockStep : ℝ)))) idealEnvironment)=_
    rw [← Unitary.conjStarAlgAut_symm]
    exact (Unitary.conjStarAlgAut ℂ _ _).apply_symm_apply idealEnvironment
  rw [inverse]
  rfl

theorem boundary_seed_diagonal_zero (R : Matrix Pair Pair ℂ) (d : Fin 2 → ℂ) :
    energy loadInteraction (boundarySeed (Matrix.kronecker R (Matrix.diagonal d)))=0 := by
  rw [boundarySeed,FreeHistory.free_received_bare,FreeHistory.bare_pc_diagonal_controller]
  exact FreeHistory.boundary_diagonal_controller _ _ _

theorem controller_flip_charged :
    conjugation controllerUnitary Powered.Dynamics.excitedController=
      Matrix.diagonal (![1,0] : Fin 2 → ℂ) := by
  rw [conjugation_apply]
  change controllerFlip*Powered.Dynamics.excitedController*controllerFlipᴴ=_
  rw [controller_flip_hermitian.eq]
  ext i j
  simp only [Matrix.mul_apply,Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    norm_num [controllerFlip,Powered.Dynamics.excitedController,Matrix.diagonal_apply]

theorem control_charged_product (R : Matrix Pair Pair ℂ) :
    conjugation sourceControl (Powered.Dynamics.chargedInput R)=
      Matrix.kronecker (conjugation phaseUnitary R) (Matrix.diagonal (![1,0] : Fin 2 → ℂ)) := by
  change Load.Quantum.localConjugation phaseUnitary controllerUnitary
    (Matrix.kronecker R Powered.Dynamics.excitedController)=_
  rw [Load.Quantum.localConjugation_tensor,controller_flip_charged]

theorem boundary_before_zero : energy loadInteraction (boundarySeed chargedSeed)=0 := by
  change energy loadInteraction
    (boundarySeed (Matrix.kronecker Powered.Producer.sourceReceivedPair (Matrix.diagonal (![0,1] : Fin 2 → ℂ))))=0
  exact boundary_seed_diagonal_zero _ _

theorem boundary_after_zero : energy loadInteraction (boundarySeed (conjugation sourceControl chargedSeed))=0 := by
  rw [chargedSeed,control_charged_product]
  exact boundary_seed_diagonal_zero _ _

theorem transported_reference_action (U : Matrix.unitaryGroup PairController ℂ)
    (rho : Matrix PairController PairController ℂ) :
    conjugation (transportedControl U) (conjugation U rho)=conjugation U (conjugation sourceControl rho) := by
  simp only [transportedControl,Environment.conjugation_comp,mul_assoc,Unitary.star_mul_self,mul_one]

theorem ideal_before_as_free :
    Incidence.bodyRead idealSixteen.toBlocks₂₂=
      conjugation (FreeHistory.freeLoad (8*(nativeClockStep : ℝ))) (boundarySeed chargedSeed) := by
  rw [boundary_seed_free,ideal_right_body_product]
  rfl

theorem ideal_after_as_free :
    Incidence.bodyRead (conjugation recoveredBodyControl idealSixteen.toBlocks₂₂)=
      conjugation (FreeHistory.freeLoad (8*(nativeClockStep : ℝ))) (boundarySeed (conjugation sourceControl chargedSeed)) := by
  rw [recoveredBodyControl,FreeHistory.pc_lift_body_read,ideal_right_body_product]
  change Load.Quantum.localConjugation recoveredPCControl (1 : Matrix.unitaryGroup (Fin 2) ℂ)
    (Matrix.kronecker (conjugation recoveredPCPhase chargedSeed) idealEnvironment)=_
  rw [Load.Quantum.localConjugation_tensor]
  have unchanged : conjugation (1 : Matrix.unitaryGroup (Fin 2) ℂ) idealEnvironment=idealEnvironment := by
    simp only [conjugation_apply,Submonoid.coe_one,star_one,Matrix.one_mul,Matrix.mul_one]
  rw [unchanged,recoveredPCControl,transported_reference_action,← boundary_seed_free]

theorem charged_seed_positive : chargedSeed.PosSemidef :=
  Powered.Dynamics.chargedInput_positive _ Powered.Producer.sourceParentState.positive

theorem ideal_boundary_before_bound :
    |energy loadInteraction (Incidence.bodyRead idealSixteen.toBlocks₂₂)| ≤
      840*(nativeClockStep : ℝ)*idealMass := by
  have bound := FreeHistory.free_boundary_energy_error (8*(nativeClockStep : ℝ)) (boundarySeed chargedSeed)
    (boundary_seed_positive _ charged_seed_positive)
  have trace : chargedSeed.trace=1 := charged_trace
  rw [boundary_before_zero,sub_zero,boundary_seed_trace _ trace,← ideal_before_as_free] at bound
  have positive : 0 ≤ 8*(nativeClockStep : ℝ) := by
    have q : 0 ≤ (nativeClockStep : ℝ) := by exact_mod_cast nativeClockStep_positive.le
    positivity
  rw [abs_of_nonneg positive] at bound
  change _ ≤ 105*(8*(nativeClockStep : ℝ))*idealMass at bound
  nlinarith only [bound]

theorem ideal_boundary_after_bound :
    |energy loadInteraction (Incidence.bodyRead (conjugation recoveredBodyControl idealSixteen.toBlocks₂₂))| ≤
      840*(nativeClockStep : ℝ)*idealMass := by
  have positive := conjugation_posSemidef sourceControl chargedSeed charged_seed_positive
  have trace : (conjugation sourceControl chargedSeed).trace=1 := (conjugation_trace _ _).trans charged_trace
  have bound := FreeHistory.free_boundary_energy_error (8*(nativeClockStep : ℝ))
    (boundarySeed (conjugation sourceControl chargedSeed)) (boundary_seed_positive _ positive)
  rw [boundary_after_zero,sub_zero,boundary_seed_trace _ trace,← ideal_after_as_free] at bound
  have nonnegative : 0 ≤ 8*(nativeClockStep : ℝ) := by
    have q : 0 ≤ (nativeClockStep : ℝ) := by exact_mod_cast nativeClockStep_positive.le
    positivity
  rw [abs_of_nonneg nonnegative] at bound
  change _ ≤ 105*(8*(nativeClockStep : ℝ))*idealMass at bound
  nlinarith only [bound]

def rightBoundaryWork : PointerJoint := Replenish.Readout.rightBlock
  (Physical.boundaryHamiltonian-conjugation (star recoveredBodyControl) Physical.boundaryHamiltonian)

theorem right_boundary_work_norm : ‖rightBoundaryWork‖ ≤ 2 := by
  have boundary : ‖Physical.boundaryHamiltonian‖ ≤ (1 : ℝ) :=
    (Blocks.EnergyFrame.body_observable_norm loadInteraction).trans
      Blocks.EnergyFrame.Inverse.actual_load_interaction_norm
  have same : ‖conjugation (star recoveredBodyControl) Physical.boundaryHamiltonian‖=
      ‖Physical.boundaryHamiltonian‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ _ (star recoveredBodyControl)) _
  exact (Replenish.Readout.right_norm _).trans ((norm_sub_le _ _).trans (by linarith only [same,boundary]))

private theorem right_work_read {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    energy (Replenish.Readout.rightBlock (H-conjugation (star U) H)) rho=
      energy H rho.toBlocks₂₂-energy H (conjugation U rho.toBlocks₂₂) := by
  rw [Replenish.Physical.right_energy]
  have pulled : energy H (conjugation U rho.toBlocks₂₂)=energy (conjugation (star U) H) rho.toBlocks₂₂ :=
    Load.Producer.StrictThermal.energy_pullback _ _ _
  rw [pulled]
  simp only [energy,Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re]

theorem right_boundary_work_read (rho : PointerJoint) :
    energy rightBoundaryWork rho=
      boundaryEnergyOf rho.toBlocks₂₂-boundaryEnergyOf (conjugation recoveredBodyControl rho.toBlocks₂₂) :=
  right_work_read Physical.boundaryHamiltonian recoveredBodyControl rho

theorem ideal_boundary_work_lower :
    -(1680*(nativeClockStep : ℝ)*idealMass) ≤ energy rightBoundaryWork idealSixteen := by
  rw [right_boundary_work_read,← boundary_body,← boundary_body]
  change -(1680*(nativeClockStep : ℝ)*idealMass) ≤
    energy loadInteraction (Incidence.bodyRead idealSixteen.toBlocks₂₂)-
      energy loadInteraction (Incidence.bodyRead (conjugation recoveredBodyControl idealSixteen.toBlocks₂₂))
  linarith only [(abs_le.mp ideal_boundary_after_bound).2,
    (abs_le.mp ideal_boundary_before_bound).1]

theorem actual_combined_work_lower :
    (1-1680*(nativeClockStep : ℝ))*idealMass-108*(nativeClockStep : ℝ) ≤
      energy rightPCWork origin.joint+energy rightBoundaryWork origin.joint := by
  have q : 0 ≤ (nativeClockStep : ℝ) := by exact_mod_cast nativeClockStep_positive.le
  have pc := complete_observer_error rightPCWork
  have boundary := complete_observer_error rightBoundaryWork
  have pcBound : 18*‖rightPCWork‖*(nativeClockStep : ℝ) ≤ 72*(nativeClockStep : ℝ) := by
    nlinarith only [right_pc_work_norm,q]
  have boundaryBound : 18*‖rightBoundaryWork‖*(nativeClockStep : ℝ) ≤ 36*(nativeClockStep : ℝ) := by
    nlinarith only [right_boundary_work_norm,q]
  have pcError := (abs_le.mp (pc.trans pcBound)).1
  have boundaryError := (abs_le.mp (boundary.trans boundaryBound)).1
  have idealPC := ideal_right_work_lower
  rw [← right_pc_work_read] at idealPC
  nlinarith only [pcError,boundaryError,idealPC,ideal_boundary_work_lower]

theorem actual_combined_work_positive :
    (2/25 : ℝ) < energy rightPCWork origin.joint+energy rightBoundaryWork origin.joint := by
  have coefficient : 0 < 1-1680*(nativeClockStep : ℝ) := by rw [nativeClockStep_exact]; norm_num
  have paid := mul_lt_mul_of_pos_left ideal_mass_lower coefficient
  have clock : (2/25 : ℝ) <
      (1-1680*(nativeClockStep : ℝ))*((1/2 : ℝ)-18*(nativeClockStep : ℝ))-108*(nativeClockStep : ℝ) := by
    rw [nativeClockStep_exact]
    norm_num
  linarith only [paid,clock,actual_combined_work_lower]

theorem recovered_body_donor (rho : Current.FullJoint) :
    donorMatrixOf (conjugation recoveredBodyControl rho)=donorMatrixOf rho := by
  unfold donorMatrixOf
  rw [show Powered.Dynamics.systemReduce (conjugation recoveredBodyControl rho)=
      conjugation (Quantum.localUnitary recoveredPCControl 1) (Powered.Dynamics.systemReduce rho) from
    Load.Quantum.systemReduce_local_conjugation _ _ _]
  change Collision.bathReduce (Quantum.localConjugation recoveredPCControl 1 _)=_
  rw [Quantum.bathReduce_local_conjugation]
  simp [conjugation_apply]

theorem recovered_body_environment (rho : Current.FullJoint) :
    Powered.Dynamics.controllerReduce (conjugation recoveredBodyControl rho)=Powered.Dynamics.controllerReduce rho := by
  change Powered.Dynamics.controllerReduce
    (Load.Quantum.localConjugation (Quantum.localUnitary recoveredPCControl 1) 1 rho)=_
  rw [Load.Quantum.controllerReduce_local_conjugation]
  simp [conjugation_apply]

theorem recovered_donor (rho : PointerJoint) :
    donorMatrixOf (bodyRead (conjugation recoveredPointerControl rho))=donorMatrixOf (bodyRead rho) := by
  rw [recovered_body_read,bodyRead]
  have additive (A B : Current.FullJoint) : donorMatrixOf (A+B)=donorMatrixOf A+donorMatrixOf B := by
    simp only [donorMatrixOf,map_add]
  rw [additive,additive,recovered_body_donor]

theorem recovered_environment (rho : PointerJoint) :
    Powered.Dynamics.controllerReduce (bodyRead (conjugation recoveredPointerControl rho))=
      Powered.Dynamics.controllerReduce (bodyRead rho) := by
  rw [recovered_body_read,bodyRead,map_add,map_add,recovered_body_environment]

theorem recovered_boundary_work (rho : PointerJoint) :
    boundaryEnergyOf (bodyRead rho)-boundaryEnergyOf (bodyRead (conjugation recoveredPointerControl rho))=
      energy rightBoundaryWork rho := by
  rw [recovered_body_read,bodyRead,boundaryEnergyOf_add,boundaryEnergyOf_add,right_boundary_work_read]
  ring

theorem recovered_total_work (current : Live.State) :
    Live.baselineEnergy current-Live.baselineEnergy (recoveredNext current)=
      energy rightPCWork current.joint+energy rightBoundaryWork current.joint := by
  rw [Live.baselineEnergy_split,Live.baselineEnergy_split,baseline_energy_split,baseline_energy_split,
    recovered_next_joint]
  have donor : donorEnergyOf (bodyRead (conjugation recoveredPointerControl current.joint))=
      donorEnergyOf (bodyRead current.joint) := congrArg (energy Powered.Producer.poweredTotalHamiltonian) (recovered_donor _)
  have environment : environmentEnergyOf (bodyRead (conjugation recoveredPointerControl current.joint))=
      environmentEnergyOf (bodyRead current.joint) := congrArg (energy (Powered.Dynamics.controllerHamiltonian 2)) (recovered_environment _)
  have pointer : pointerEnergy (conjugation recoveredPointerControl current.joint)=pointerEnergy current.joint :=
    congrArg (fun x : ℝ => 2*x) (blockUnitary_preserves_oneRead 1 recoveredBodyControl current.joint)
  rw [donor,environment,pointer,right_pc_work_read]
  linarith only [recovered_pc_work current.joint,recovered_boundary_work current.joint]

theorem recovered_actual_total_gain :
    (2/25 : ℝ) < Live.baselineEnergy origin-Live.baselineEnergy (recoveredNext origin) := by
  rw [recovered_total_work]
  exact actual_combined_work_positive

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery
