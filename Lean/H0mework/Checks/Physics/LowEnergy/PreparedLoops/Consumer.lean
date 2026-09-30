import H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Scalar

set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.Consumer
open QuantizationCheck.Fermion Fermion ClosedLoops StateGreen CoframeResponse
open YangMills.FullPairing DiracExteriorMatterAction ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair StageNineDynamicBreakingVacuum
noncomputable section
attribute [local instance] Fermion.fullIndexOrder
local instance preparedLoopIndexDecidableEq : DecidableEq Quantum.Index := Classical.decEq _

theorem actual_unit_word (point : BasePoint) : read (preparedVector point) (fullWord [])=1 := by
  simpa only [fullWord,List.map_nil,List.prod_nil,read_one] using preparedVector_unit point

theorem actual_weight_is_not_bare_trace (point : BasePoint) :
    read (preparedVector point) (fullWord [])≠loopTrace (1 : Mother) := by
  rw [actual_unit_word]
  have matrix : Quantum.operatorMatrix (1 : Mother)=1 := Quantum.operatorMatrix.map_one
  rw [loopTrace,matrix,Matrix.trace_one,Quantum.index_card]
  norm_num

theorem native_weighted_all_words (point : BasePoint) (steps : List SourceStep) :
    Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer point)
      (Stage9DEF.Compatibility.responseMatrix (pairedMother 1
        (sourceWordMother (weightedWord Stage9C.Material.SpinPair.actual point (fullSteps point steps)))))=
      read (preparedVector point) (weightedWord Stage9C.Material.SpinPair.actual point (diagonalSteps point steps)) :=
  source_weighted_Stage10 point steps

theorem actual_scalar_weighted_zero (point : BasePoint) (before after : List SourceStep) :
    read (preparedVector point) (weightedWord actual point
      (fullSteps point before++StageNineDiracDualYukawaSpinJurisdiction.diracDualRightChiralYukawaAction
        (scalarCoordinateEquiv.symm (actual.scalar point))::fullSteps point after))=0 :=
  source_scalar_weighted_word point before after (actual.scalar point)

theorem source_reader_raw_identity (point : BasePoint) :
    ((|(actual.coframe point).det| : ℝ) : ℂ)*actual.conjugateMatter point
      (Exchange.currentOperator (actual.coframe point) 1 (sourceColorP286Generator 0) (actual.matter point))=
      4*inner ℂ (prepared point) (operator (sourceReader point 1 (sourceColorP286Generator 0)) (prepared point)) :=
  sourceReader_original point 1 (sourceColorP286Generator 0)

theorem source_scalar_transfer_vanishes (point : BasePoint) (scalar : ScalarCoordinateCarrier)
    (plus minus : SourceStep) :
    transferRead point (scalarForce point scalar) (sourceReader point 1 (sourceColorP286Generator 0))
      (Triangular.fullResolvent actual point plus.momentum (Retarded.spectralParameter plus.energy plus.damping))
      (Triangular.fullResolvent actual point minus.momentum (Retarded.spectralParameter minus.energy minus.damping))=0 :=
  source_scalar_gauge_transfer_zero point scalar 1 (sourceColorP286Generator 0) plus minus

theorem original_return_stays_visible :
    Stage9DEF.Compatibility.vectorRead 0
      (Stage9DEF.Compatibility.responseMatrix Contact.ReturnChannel.detectedAction)≠0 :=
  Contact.ReturnChannel.detected_read_nonzero

#print axioms actual_unit_word
#print axioms actual_weight_is_not_bare_trace
#print axioms native_weighted_all_words
#print axioms actual_scalar_weighted_zero
#print axioms source_reader_raw_identity

#print axioms source_scalar_transfer_vanishes
#print axioms original_return_stays_visible

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops.Consumer
