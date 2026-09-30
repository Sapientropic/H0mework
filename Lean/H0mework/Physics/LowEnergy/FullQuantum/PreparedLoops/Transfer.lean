import H0mework.Physics.LowEnergy.FullQuantum.PreparedLoops.Native
import H0mework.Physics.LowEnergy.FullQuantum.StateResponse.TransferNative

/-! The same incoming-zero / intermediate transfer carrier retains the source grading at the final prepared read. -/
set_option autoImplicit false
open scoped InnerProductSpace Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops
open QuantizationCheck.Fermion Fermion ClosedLoops StateGreen StateResponse CoframeResponse Triangular
open YangMills.FullPairing DiracExteriorMatterAction ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal SU7MotherLieAlgebra
noncomputable section
attribute [local instance] Fermion.fullIndexOrder StateResponse.transferIndexOrder

def transferRead (point : BasePoint) (T B Rplus Rminus : Mother) : ℂ :=
  transferNativeRead point
    (connectedWord (modeVector 0 (preparedVector point))
      (transferReader (Quantum.operatorMatrix B) (Quantum.operatorMatrix Rplus) (Quantum.operatorMatrix Rminus))
      (transferForce (Quantum.operatorMatrix T))-
    connectedWord (modeVector 0 (preparedVector point))
      (transferForce (Quantum.operatorMatrix T))
      (transferReader (Quantum.operatorMatrix B) (Quantum.operatorMatrix Rplus) (Quantum.operatorMatrix Rminus)))

theorem prepared_matrix_pair (point : BasePoint) (A : Mother) :
    modePair (preparedVector point) (Quantum.operatorMatrix A*ᵥpreparedVector point)=
      inner ℂ (prepared point) (operator A (prepared point)) := by
  have read := fullWord_read point [A]
  simpa only [fullWord,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,read_quantize] using read

theorem transferRead_generated (point : BasePoint) (T B Rplus Rminus : Mother) :
    transferRead point T B Rplus Rminus=
      inner ℂ (prepared point) (operator (B*Rplus*T) (prepared point))-
        inner ℂ (prepared point) (operator (T*Rminus*B) (prepared point)) := by
  rw [transferRead,source_transfer_response]
  have product (A B C : Mother) : Quantum.operatorMatrix A*Quantum.operatorMatrix B*Quantum.operatorMatrix C=
      Quantum.operatorMatrix (A*B*C) := by
    change _=Quantum.operatorMatrix ((A.comp B).comp C)
    rw [Quantum.matrix_composition,Quantum.matrix_composition]
  rw [product,product,prepared_matrix_pair,prepared_matrix_pair]

theorem transferRead_expansion (point : BasePoint) (T T0 B B0 Rplus Rplus0 Rminus Rminus0 : Mother)
    (force : Expansion T T0) (reader : Expansion B B0)
    (plus : Expansion Rplus Rplus0) (minus : Expansion Rminus Rminus0) :
    transferRead point T B Rplus Rminus=transferRead point T0 B0 Rplus0 Rminus0 := by
  rw [transferRead_generated,transferRead_generated,
    expansion_prepared point _ _ ((reader.mul plus).mul force),
    expansion_prepared point _ _ ((force.mul minus).mul reader)]

def sourceForce (point : BasePoint) (direction : LorentzianIndex) (data : P286LieBlockData) : Mother :=
  (-Complex.I) • (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point)*
    Exchange.currentOperator (actual.coframe point) direction data)

def sourceReader (point : BasePoint) (direction : LorentzianIndex) (data : P286LieBlockData) : Mother :=
  (-1 : ℂ) • (boundaryWeight actual point*sourceForce point direction data)

theorem sourceForce_grade (point : BasePoint) (direction : LorentzianIndex) (data : P286LieBlockData) :
    Commute MixedSymbol.degreeSix (sourceForce point direction data) :=
  ((grade_principal_inverse 0 actual point).mul_right (original_gauge_vertex (actual.coframe point) direction data).1).smul_right _

theorem sourceReader_grade (point : BasePoint) (direction : LorentzianIndex) (data : P286LieBlockData) :
    Commute MixedSymbol.degreeSix (sourceReader point direction data) :=
  ((boundary_grade actual point).mul_right (sourceForce_grade point direction data)).smul_right _

theorem sourceReader_original (point : BasePoint) (direction : LorentzianIndex) (data : P286LieBlockData) :
    ((|(actual.coframe point).det| : ℝ) : ℂ)*actual.conjugateMatter point
      (Exchange.currentOperator (actual.coframe point) direction data (actual.matter point))=
      4*inner ℂ (prepared point) (operator (sourceReader point direction data) (prepared point)) := by
  have original := original_dual_full_CAR actual point 0 0
    (Exchange.currentOperator (actual.coframe point) direction data)
  simp only [canonicalDual,LinearMap.comp_apply,neg_zero,primal_zero,
    currentCoframeMatterTemporalPrincipalInverse_right _ (actual_noncharacteristic point)] at original
  rw [boundaryWord_pair] at original
  simp only [boundaryInsertion,LinearMap.comp_apply,neg_zero,primal_zero] at original
  change _= -4*Quantum.coordinatePair (preparedMatter point)
    ((boundaryWeight actual point*sourceForce point direction data) (preparedMatter point)) at original
  rw [Quantum.coordinatePair_full,← natural_inner,← operator_coordinates,preparedMatter_original] at original
  rw [sourceReader,operator_smul,smul_apply,inner_smul_right,original]
  ring

theorem native_transfer_yukawa_independent (point : BasePoint) (forceDirection readerDirection : LorentzianIndex)
    (forceData readerData : P286LieBlockData) (plus minus : SourceStep) :
    transferRead point (sourceForce point forceDirection forceData) (sourceReader point readerDirection readerData)
      (fullResolvent actual point plus.momentum (Retarded.spectralParameter plus.energy plus.damping))
      (fullResolvent actual point minus.momentum (Retarded.spectralParameter minus.energy minus.damping))=
    transferRead point (sourceForce point forceDirection forceData) (sourceReader point readerDirection readerData)
      (freeResolvent actual point plus.momentum (Retarded.spectralParameter plus.energy plus.damping))
      (freeResolvent actual point minus.momentum (Retarded.spectralParameter minus.energy minus.damping)) :=
  transferRead_expansion point _ _ _ _ _ _ _ _
    (Expansion.refl _ (sourceForce_grade point forceDirection forceData))
    (Expansion.refl _ (sourceReader_grade point readerDirection readerData))
    (source_resolvent actual point plus.momentum _ (plus.regular point).2)
    (source_resolvent actual point minus.momentum _ (minus.regular point).2)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedLoops
