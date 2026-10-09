import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedFieldReturn

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalLockedCurrentFirstResidue
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction DiracCliffordRepresentation StageNineHolonomicField
open SourceQuantumGaugeSliceCoordinates NativeHistoryGrade
open PreparationVacuumPhysicalElectromagneticDirection PreparationVacuumGaugeSourceInjection
open PreparationVacuumSourceActionJets PreparationVacuumSourceFieldFamily PreparationVacuumActualFieldQuantization
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open SourceQuantumScalarChart GaussFockLabel GaussYukawaGrade GaussHistoryHilbert
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open scoped Matrix BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local irreducible] sourceLockedAction sourceLockedCoefficient sourceLockedSymbol sourceLockedFiber

/-- Both original source actions preserve occupation grade on the full matter carrier. -/
theorem sourceLockedAction_degree (i : Fin 3) :
    Commute MixedSymbol.degreeSix (sourceLockedAction i) := by
  change MixedSymbol.degreeSix*sourceLockedAction i=sourceLockedAction i*MixedSymbol.degreeSix
  unfold sourceLockedAction
  rw [mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
  simp only [Module.End.mul_eq_comp,MixedSymbol.degreeSix_gauge,MixedSymbol.degreeSix_spin]

private def primalPreserves (A : SourceMatrix) : Prop:=∀i j,
  ((if isSix i then (1:ℂ) else 0)-(if isSix j then (1:ℂ) else 0))*A i j=0

private theorem primal_smul (A : SourceMatrix) (paid : primalPreserves A) (c : ℂ) :
    primalPreserves (c • A) := by
  intro i j
  change _*(c*A i j)=0
  rw [mul_left_comm,paid i j,mul_zero]

private theorem primal_mul (A B : SourceMatrix) (left : primalPreserves A) (right : primalPreserves B) :
    primalPreserves (A*B) := by
  intro i j
  rw [Matrix.mul_apply,Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro k _
  calc
    _=(((if isSix i then (1:ℂ) else 0)-(if isSix k then (1:ℂ) else 0))*A i k)*B k j+
      A i k*(((if isSix k then (1:ℂ) else 0)-(if isSix j then (1:ℂ) else 0))*B k j) := by ring
    _=0 := by rw [left i k,right k j,zero_mul,mul_zero,add_zero]

private theorem primal_mother (A : Module.End ℂ DiracExteriorMatterCarrier)
    (paid : Commute MixedSymbol.degreeSix A) : primalPreserves (Quantum.operatorMatrix A) := by
  intro i j
  simpa only [Nat.cast_zero,sub_zero] using matrix_grade A 0
    (by simpa only [Nat.cast_zero,zero_smul,add_zero] using paid.eq) i j

private theorem primal_coefficient (mu : Fin 4) (e : LorentzianCoframe) :
    primalPreserves (coefficientMatrix mu e) := by
  unfold coefficientMatrix
  apply primal_smul
  exact primal_mother _ (MixedSymbol.degreeSix_spin _)

private theorem primal_density : primalPreserves densityActionMatrix := by
  unfold densityActionMatrix
  apply primal_smul
  apply primal_mother
  change MixedSymbol.degreeSix*YangMills.FullPairing.flipMatter=
    YangMills.FullPairing.flipMatter*MixedSymbol.degreeSix
  apply LinearMap.ext
  intro v
  funext spin
  rfl

private theorem primal_lockedCoefficient (mu : Fin 4) (i : Fin 3) (s : ActionState) :
    primalPreserves (sourceLockedCoefficient mu i s) := by
  unfold sourceLockedCoefficient
  exact primal_mul _ _ primal_density (primal_smul _
    (primal_mul _ _ (primal_coefficient mu s.1) (primal_mother _ (sourceLockedAction_degree i)))
    (stateVolume s))

private theorem full_branches (A : SourceMatrix) (paid : primalPreserves A) :
    Preserves (SourceRealScalarFock.branches A) := by
  intro i j
  simpa only [charge,Nat.cast_zero,sub_zero] using branches_grade A 0
    (by intro u v;simpa only [Nat.cast_zero,sub_zero] using paid u v) i j

private theorem opposite_preserves : Preserves oppositeDual := by
  intro i j
  cases i <;> cases j <;> simp [charge,oppositeDual,Matrix.fromBlocks,Matrix.one_apply]
  all_goals intro same;subst same;ring

/-- The actual density, coframe and independent-dual branches jointly preserve the source grade. -/
theorem sourceLockedSymbol_gradeZero (mu : Fin 4) (i : Fin 3) (s : ActionState) :
    Preserves (sourceLockedSymbol mu i s) := by
  unfold sourceLockedSymbol
  exact preserves_mul opposite_preserves (full_branches _ (primal_lockedCoefficient mu i s))

theorem sourceLockedFiber_gradeZero (mu : Fin 4) (i : Fin 3) (z : SourceCoordinateSlice) :
    Commute fiberGrade (sourceLockedFiber mu i z) := by
  unfold sourceLockedFiber fiberGrade
  exact blockWeight_quantized _ _ (sourceLockedSymbol_gradeZero mu i (sourceState z))

/-- Every occupation/grade block is retained; no prepared-state homogeneity is supplied. -/
theorem sourceLockedFiber_blocks (mu : Fin 4) (i : Fin 3) (z : SourceCoordinateSlice)
    (g : NativeHistoryGrade.Label) : Commute (GaussCoreLabel.fiberPiece g) (sourceLockedFiber mu i z) := by
  unfold sourceLockedFiber GaussCoreLabel.fiberPiece
  exact blockWeight_quantized _ _ (sourceLockedSymbol_gradeZero mu i (sourceState z))

end LowEnergy.PreparationVacuumPhysicalLockedCurrentFirstResidue
