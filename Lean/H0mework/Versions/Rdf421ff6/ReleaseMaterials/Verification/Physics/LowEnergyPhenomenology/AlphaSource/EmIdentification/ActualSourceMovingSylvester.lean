import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualRestLightSylvester

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualMovingSourceLight
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource SourceQuantumFockGauge
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open ActualSourcePreparationBridge ActualSourceLightCircuit
open PreparationVacuumElectromagneticIdentity PreparationVacuumActionFieldLift
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization
open PreparationVacuumSourceFieldFamily PreparationVacuumRawJointFeedback
open PreparationVacuumGaugeSourceInjection FullQuantum.StateGreen
open PreparationVacuumJointFieldResponse PreparationVacuumNonlinearFieldCurve
open GaussHistoryHilbert
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
local instance instDecidableEqIndex_actualSourceMovingSylvester : DecidableEq Quantum.Index:=Classical.decEq _
local instance instDecidableEqMode_actualSourceMovingSylvester : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local irreducible] restPrimalWave
local instance instNormedAddCommGroupLorentzianCoframe_actualSourceMovingSylvester : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance instSeminormedAddCommGroupLorentzianCoframe_actualSourceMovingSylvester : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance instNormedSpaceRealLorentzianCoframe_actualSourceMovingSylvester : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance finiteMaterial : FiniteDimensional ℂ FullMaterialMatrix:=Matrix.finiteDimensional
local instance finiteRest : FiniteDimensional ℂ RestMatterMatrix:=Matrix.finiteDimensional

abbrev HSIndex:=Fin 4×Fin 4
abbrev HS:=EuclideanSpace ℂ HSIndex
abbrev HSOperator:=HS→L[ℂ]HS
abbrev HSMatrix:=Matrix HSIndex HSIndex ℂ
local instance finiteHSMatrix : FiniteDimensional ℂ HSMatrix:=Matrix.finiteDimensional
local instance opReal : NormedAlgebra ℝ HSOperator:=NormedAlgebra.restrictScalars ℝ ℂ _

/-- Row-major material observable coordinates are exactly the original two-four HS space. -/
def sourceHSCoordinates : RestMatterMatrix≃ₗ[ℂ]HS where
  toFun:=fun A=>WithLp.toLp 2 (fun i=>A i.1 i.2)
  invFun:=fun v i j=>v (i,j)
  left_inv:=fun _=>rfl
  right_inv:=fun _=>rfl
  map_add':=fun _ _=>rfl
  map_smul':=fun _ _=>rfl

private def hsQuantizer : HSMatrix→ₗ[ℂ]HSOperator where
  toFun:=fun A=>(Matrix.toEuclideanLin A).toContinuousLinearMap
  map_add':=by
    intro A B
    apply ContinuousLinearMap.ext
    intro v
    apply PiLp.ext
    intro i
    change ((A+B)*ᵥWithLp.ofLp v) i=(A*ᵥWithLp.ofLp v) i+(B*ᵥWithLp.ofLp v) i
    rw [Matrix.add_mulVec];rfl
  map_smul':=by
    intro q A
    apply ContinuousLinearMap.ext
    intro v
    apply PiLp.ext
    intro i
    change ((q • A)*ᵥWithLp.ofLp v) i=q*(A*ᵥWithLp.ofLp v) i
    rw [Matrix.smul_mulVec];rfl

private def hsSylvesterMatrix : (RestMatterMatrix×RestMatterMatrix)→ₗ[ℂ]HSMatrix where
  toFun:=fun H i j=>(Complex.I/(sourceMaterialClock:ℂ))*
    ((if i.2=j.2 then H.1 i.1 j.1 else 0)-(if i.1=j.1 then H.2 j.2 i.2 else 0))
  map_add':=by
    intro A B
    ext i j
    by_cases l : i.2=j.2 <;> by_cases r : i.1=j.1 <;>
      simp [l,r] <;> ring
  map_smul':=by
    intro q A
    ext i j
    by_cases l : i.2=j.2 <;> by_cases r : i.1=j.1 <;>
      simp [l,r] <;> ring

def sourceHSSylvester : (RestMatterMatrix×RestMatterMatrix)→L[ℂ]HSOperator :=
  (hsQuantizer.comp hsSylvesterMatrix).toContinuousLinearMap

theorem source_HS_sylvester_value (HL HR B : RestMatterMatrix) :
    sourceHSSylvester (HL,HR) (sourceHSCoordinates B)=
      sourceHSCoordinates ((Complex.I/(sourceMaterialClock:ℂ)) • (HL*B-B*HR)) := by
  apply PiLp.ext
  intro i
  change (∑j : HSIndex,(Complex.I/(sourceMaterialClock:ℂ))*
    ((if i.2=j.2 then HL i.1 j.1 else 0)-(if i.1=j.1 then HR j.2 i.2 else 0))*B j.1 j.2)=
      (Complex.I/(sourceMaterialClock:ℂ))*((HL*B) i.1 i.2-(B*HR) i.1 i.2)
  simp only [mul_assoc,←Finset.mul_sum]
  apply congrArg (fun q : ℂ=>(Complex.I/(sourceMaterialClock:ℂ))*q)
  simp only [Fintype.sum_prod_type,sub_mul,Finset.sum_sub_distrib,ite_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,if_true]
  have right : (∑j : Fin 4,∑k : Fin 4,if i.1=j then HR k i.2*B j k else 0)=
      ∑k : Fin 4,B i.1 k*HR k i.2 := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [right]
  rfl

private def blockRestrictionMap (block : RestBlock) : FullMaterialMatrix→L[ℂ]RestMatterMatrix :=
  (show FullMaterialMatrix→ₗ[ℂ]RestMatterMatrix from
    {toFun:=restBlockRestriction block
     map_add':=rest_block_restriction_add block
     map_smul':=rest_block_restriction_smul block}).toContinuousLinearMap

def actualSourceBlockHamiltonian (block : RestBlock) (p : PhysicalMomentum) (s : ActionState) : RestMatterMatrix :=
  blockRestrictionMap block (sourceSymbol p s)

def actualMovingSourceSylvester (block : RestBlock) (pL pR : PhysicalMomentum) (u : JointParameter) : HSOperator :=
  sourceHSSylvester (actualSourceBlockHamiltonian block pL (ambientState u),
    actualSourceBlockHamiltonian block pR (ambientState u))

def actualMovingSourceSylvesterContact (block : RestBlock) (pL pR : PhysicalMomentum)
    (force : Field289) (z : SourceCoordinateSlice) : HSOperator :=
  sourceHSSylvester (blockRestrictionMap block (symbolFirst pL (sourceState z) (fieldDirection force)),
    blockRestrictionMap block (symbolFirst pR (sourceState z) (fieldDirection force)))

theorem actual_source_block_hamiltonian_at_source (side : Fin 2) (p : PhysicalMomentum) :
    actualSourceBlockHamiltonian (false,side) p (sourceState GaussHistoryHilbert.sourcePoint.val)=
      actualMatterCarrierHamiltonian 0 side p :=
  source_rest_primal_hamiltonian side p

/-- The independently conjugate material branch keeps the original -p Hamiltonian and its source sign. -/
theorem actual_source_dual_block_hamiltonian (side : Fin 2) (p : PhysicalMomentum) (s : ActionState) :
    actualSourceBlockHamiltonian (true,side) p s=
      -(actualSourceBlockHamiltonian (false,side) (-p) s).map star := by
  ext row column
  change restBlockRestriction (true,side) (realFourierMatrix (stateHamiltonian s) p) row column=
    -star (restBlockRestriction (false,side) (realFourierMatrix (stateHamiltonian s) (-p)) row column)
  simp only [restBlockRestriction,Matrix.mul_apply,Matrix.conjTranspose_apply,restBlockFrame,
    restModeWave,realFourierMatrix,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    Bool.false_eq_true,if_false,if_true,star_zero,mul_zero,zero_mul,
    Finset.sum_const_zero,add_zero,zero_add,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.neg_apply,Matrix.map_apply,
    star_star]
  simp only [mul_neg,neg_mul,Finset.sum_neg_distrib]
  apply congrArg Neg.neg
  simp only [star_sum,star_mul,star_star]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Both momenta and the complete actual field direction generate the changing source Sylvester. -/
theorem actual_moving_source_sylvester_contact_generated (block : RestBlock) (pL pR : PhysicalMomentum)
    (force : Field289) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>actualMovingSourceSylvester block pL pR (r • force,z.val))
      (actualMovingSourceSylvesterContact block pL pR force z.val) 0 := by
  have valid : sourceState z.val∈validStates:=sourceState_valid z
  have left:=(blockRestrictionMap block|>.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (symbol_first_generated pL (sourceState z.val) (fieldDirection force) valid)
  have right:=(blockRestrictionMap block|>.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (symbol_first_generated pR (sourceState z.val) (fieldDirection force) valid)
  have original:=(sourceHSSylvester.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (left.prodMk right)
  have ray (r : ℝ) : ambientState (r • force,z.val)=sourceState z.val+r • fieldDirection force := by
    simp only [ambientState,map_smul];rfl
  have same : (fun r : ℝ=>actualMovingSourceSylvester block pL pR (r • force,z.val))=
      fun r : ℝ=>sourceHSSylvester
        (actualSourceBlockHamiltonian block pL (sourceState z.val+r • fieldDirection force),
          actualSourceBlockHamiltonian block pR (sourceState z.val+r • fieldDirection force)) := by
    funext r;unfold actualMovingSourceSylvester;rw [ray]
  rw [same]
  exact original

/-- The complete source symbol varies smoothly in the original joint field/configuration parameter. -/
theorem actual_moving_source_sylvester_smooth (block : RestBlock) (pL pR : PhysicalMomentum)
    (u : JointParameter) (valid : ambientState u∈validStates) :
    ContDiffAt ℝ ∞ (actualMovingSourceSylvester block pL pR) u := by
  have left:=((blockRestrictionMap block).restrictScalars ℝ).contDiff.contDiffAt.comp u
    ((sourceSymbol_smooth pL (ambientState u) valid).comp u ambientState_smooth.contDiffAt)
  have right:=((blockRestrictionMap block).restrictScalars ℝ).contDiff.contDiffAt.comp u
    ((sourceSymbol_smooth pR (ambientState u) valid).comp u ambientState_smooth.contDiffAt)
  exact (sourceHSSylvester.restrictScalars ℝ).contDiff.contDiffAt.comp u (left.prodMk right)

end LowEnergy.GaussComposite.ActualMovingSourceLight
