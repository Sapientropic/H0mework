import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePoleChargeObservation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstPoleGaugeVertex
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalNormalizedFullField PreparationPhysicalPoleChargeMatrix
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedControl PreparationVacuumFullOriginResponse
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumSourceFieldFamily
open PreparationVacuumGaugeSourceInjection PreparationVacuumLowerClassical PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumNativeSlowCoupling
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open SourceQuantumScalarChart GaussNativeMatter GaussHistoryHilbert
open FullQuantum.CoframeResponse FullQuantum.StateGreen CanonicalGradedSpatialSource
open DiracCliffordRepresentation DiracExteriorMatterAction
open scoped Matrix BigOperators Topology
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three
local instance : DecidableEq Quantum.Index:=Classical.decEq _

private theorem sourceFirst_unused (k : Fin 4) (row : Fin 289)
    (outside : row.val<9 ∨ (57≤row.val ∧ row.val<73) ∨ (121≤row.val ∧ row.val<217)) :
    sourceEnergyAxisField 1 k row=0 := by
  simp (disch := omega) [sourceEnergyAxisField,sourceEnergyChannelTerms,sourceMatrix,SourceTerm.matrix]

/-- These three vanishing sectors are computed from literal col1; matter, independent dual and gauge-B are retained. -/
theorem sourceFirstGauge_sectors (k : Fin 4) :
    fieldCoframe (sourceEnergyAxisField 1 k)=0 ∧
    fieldScalar (sourceEnergyAxisField 1 k)=0 ∧
    fieldLorentz (sourceEnergyAxisField 1 k)=0 := by
  constructor
  · ext a mu
    exact sourceFirst_unused k _ (by simp only [coframeSlot];omega)
  constructor
  · unfold fieldScalar
    apply Finset.sum_eq_zero
    intro a _
    rw [sourceFirst_unused k _ (by simp only [scalarSlot];omega),zero_smul]
  · ext mu a
    exact sourceFirst_unused k _ (by simp only [lorentzSlot];omega)

def sourceFirstTemporalCoefficients : Fin 12→ℝ :=
  Pi.single 6 (6/11)+Pi.single 7 (-5/11)+Pi.single 10 (3/11)+Pi.single 11 (5/11)

def sourceFirstSpatialCoefficients : Fin 12→ℝ :=
  Pi.single 6 (39/67)+Pi.single 7 (-34/67)+Pi.single 10 (15/67)+Pi.single 11 (25/67)

def sourceFirstLongitudinalCoefficients : Fin 12→ℝ :=
  Pi.single 6 (36/67)+Pi.single 7 (-31/67)+Pi.single 10 (15/67)+Pi.single 11 (25/67)

def sourceFirstGaugeCoefficients (k mu : Fin 4) : Fin 12→ℝ :=
  (if k=0 ∧ mu=0 then sourceFirstTemporalCoefficients else 0)+
  (if k=1 ∧ mu=1 then sourceFirstSpatialCoefficients else 0)+
  (if k=2 ∧ mu=2 then sourceFirstSpatialCoefficients else 0)+
  (if k=3 ∧ mu=3 then sourceFirstLongitudinalCoefficients else 0)+
  (if k=1 ∧ mu=3 then Pi.single 1 (-3/67) else 0)+
  (if k=2 ∧ mu=3 then Pi.single 0 (-3/67) else 0)

private theorem sourceFirstGauge_slots_0 (k : Fin 4) (a : Fin 12) :
    sourceEnergyAxisField 1 k (gaugeSlot 0 a)=sourceFirstGaugeCoefficients k 0 a := by
  change (sourceMatrix sourceEnergyChannelTerms (Pi.single k 1) (gaugeSlot 0 a) (1:Fin 289)).re=_
  rw [←rowTerms_entry sourceEnergyChannelTerms (Pi.single k 1) (gaugeSlot 0 a) (1:Fin 289)]
  fin_cases a <;> norm_num [rowTerms,sourceEnergyChannelTerms,gaugeSlot]
  all_goals fin_cases k <;>
    norm_num only [sourceFirstGaugeCoefficients,sourceFirstTemporalCoefficients,sourceFirstSpatialCoefficients,
      sourceFirstLongitudinalCoefficients,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Matrix.add_apply,Matrix.zero_apply,
      Pi.add_apply,Pi.single_apply,ite_apply,Pi.zero_apply,Fin.ext_iff] <;>
    norm_num [coefficientValue,Powers.value]
  all_goals simp only [Matrix.single_apply,Pi.single_apply,Fin.ext_iff]
  all_goals norm_num

private theorem sourceFirstGauge_slots_1 (k : Fin 4) (a : Fin 12) :
    sourceEnergyAxisField 1 k (gaugeSlot 1 a)=sourceFirstGaugeCoefficients k 1 a := by
  change (sourceMatrix sourceEnergyChannelTerms (Pi.single k 1) (gaugeSlot 1 a) (1:Fin 289)).re=_
  rw [←rowTerms_entry sourceEnergyChannelTerms (Pi.single k 1) (gaugeSlot 1 a) (1:Fin 289)]
  fin_cases a <;> norm_num [rowTerms,sourceEnergyChannelTerms,gaugeSlot]
  all_goals fin_cases k <;>
    norm_num only [sourceFirstGaugeCoefficients,sourceFirstTemporalCoefficients,sourceFirstSpatialCoefficients,
      sourceFirstLongitudinalCoefficients,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Matrix.add_apply,Matrix.zero_apply,
      Pi.add_apply,Pi.single_apply,ite_apply,Pi.zero_apply,Fin.ext_iff] <;>
    norm_num [coefficientValue,Powers.value]
  all_goals simp only [Matrix.single_apply,Pi.single_apply,Fin.ext_iff]
  all_goals norm_num

private theorem sourceFirstGauge_slots_2 (k : Fin 4) (a : Fin 12) :
    sourceEnergyAxisField 1 k (gaugeSlot 2 a)=sourceFirstGaugeCoefficients k 2 a := by
  change (sourceMatrix sourceEnergyChannelTerms (Pi.single k 1) (gaugeSlot 2 a) (1:Fin 289)).re=_
  rw [←rowTerms_entry sourceEnergyChannelTerms (Pi.single k 1) (gaugeSlot 2 a) (1:Fin 289)]
  fin_cases a <;> norm_num [rowTerms,sourceEnergyChannelTerms,gaugeSlot]
  all_goals fin_cases k <;>
    norm_num only [sourceFirstGaugeCoefficients,sourceFirstTemporalCoefficients,sourceFirstSpatialCoefficients,
      sourceFirstLongitudinalCoefficients,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Matrix.add_apply,Matrix.zero_apply,
      Pi.add_apply,Pi.single_apply,ite_apply,Pi.zero_apply,Fin.ext_iff] <;>
    norm_num [coefficientValue,Powers.value]
  all_goals simp only [Matrix.single_apply,Pi.single_apply,Fin.ext_iff]
  all_goals norm_num

private theorem sourceFirstGauge_slots_3 (k : Fin 4) (a : Fin 12) :
    sourceEnergyAxisField 1 k (gaugeSlot 3 a)=sourceFirstGaugeCoefficients k 3 a := by
  change (sourceMatrix sourceEnergyChannelTerms (Pi.single k 1) (gaugeSlot 3 a) (1:Fin 289)).re=_
  rw [←rowTerms_entry sourceEnergyChannelTerms (Pi.single k 1) (gaugeSlot 3 a) (1:Fin 289)]
  fin_cases a <;> norm_num [rowTerms,sourceEnergyChannelTerms,gaugeSlot]
  all_goals fin_cases k <;>
    norm_num only [sourceFirstGaugeCoefficients,sourceFirstTemporalCoefficients,sourceFirstSpatialCoefficients,
      sourceFirstLongitudinalCoefficients,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Matrix.add_apply,Matrix.zero_apply,
      Pi.add_apply,Pi.single_apply,ite_apply,Pi.zero_apply,Fin.ext_iff] <;>
    norm_num [coefficientValue,Powers.value]
  all_goals simp only [Matrix.single_apply,Pi.single_apply,Fin.ext_iff]
  all_goals norm_num

/-- All48 gauge slots on each of the four actual real axes are returned from the original full200 table. -/
theorem sourceFirstGauge_slots (k mu : Fin 4) (a : Fin 12) :
    sourceEnergyAxisField 1 k (gaugeSlot mu a)=sourceFirstGaugeCoefficients k mu a := by
  fin_cases mu
  · exact sourceFirstGauge_slots_0 k a
  · exact sourceFirstGauge_slots_1 k a
  · exact sourceFirstGauge_slots_2 k a
  · exact sourceFirstGauge_slots_3 k a

def sourceFirstGaugeConnection (k mu : Fin 4) : NativeLie :=
  ∑a : Fin 12,sourceFirstGaugeCoefficients k mu a • originalUnit a

theorem sourceFirstGauge_generated (k mu : Fin 4) :
    fieldGauge (sourceEnergyAxisField 1 k) mu=sourceFirstGaugeConnection k mu := by
  simp only [fieldGauge,sourceFirstGauge_slots,sourceFirstGaugeConnection]

/-- The Hamiltonian restriction consumes the real source field; its other full289 components are not set to zero. -/
theorem sourceFirstGauge_state (k : Fin 4) :
    fieldDirection (sourceEnergyAxisField 1 k)=
      (0,(fun mu=>nativePrimal (sourceFirstGaugeConnection k mu)),0) := by
  rw [←stateDirection_source]
  change (fieldCoframe (sourceEnergyAxisField 1 k),
    (fun mu=>spinLinear mu (fieldLorentz (sourceEnergyAxisField 1 k))+
      nativePrimal (fieldGauge (sourceEnergyAxisField 1 k) mu)),
      scalarLinear (fieldScalar (sourceEnergyAxisField 1 k)))=_
  rw [(sourceFirstGauge_sectors k).1,(sourceFirstGauge_sectors k).2.1,(sourceFirstGauge_sectors k).2.2]
  simp only [sourceFirstGauge_generated,map_zero,zero_add]

/-- The complete first-pole column returns the original full504 connection energy, before actual external preparation. -/
theorem sourceFirstGauge_axis_energy (p : PhysicalMomentum) (k : Fin 4) :
    sourceNormalizedEnergySymbol p (sourceState sourcePoint.val) (fieldDirection (sourceEnergyAxisField 1 k))=
      SourceRealScalarFock.branches ((-Complex.I) •
        (Ring.inverse (principalMatrix (sourceState sourcePoint.val).1)*
          (∑mu : Fin 4,coefficientMatrix mu (sourceState sourcePoint.val).1*
            nativePrimal (sourceFirstGaugeConnection k mu)))) := by
  rw [sourceFirstGauge_state,sourceNormalizedEnergySymbol_connection p _
    (PreparationVacuumNonlinearFieldCurve.sourceState_valid sourcePoint)]

end LowEnergy.PreparationPhysicalFirstPoleGaugeVertex
