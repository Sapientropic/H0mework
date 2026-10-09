import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedSecondPacket
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeBoundaryNumerator

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumChargedLongRangeRead
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumChargedSpatialResponse PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumObservedPoleTensor
open PreparationVacuumObservedBoundaryResidue PreparationVacuumQuantumSlowResidue
open PreparationVacuumFullSlowFieldResponse PreparationVacuumWholeOrigin
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumNativeSlowCoupling PreparationVacuumPhysicalFeedback
open PreparationVacuumElectromagneticIdentity CanonicalGradedSpatialSource Filter Set
open PreparationVacuumCausalPoleResponse PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalElectromagneticDirection
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] sourceChargedNativeFrameJet sourceActualNativeResidue sourceFullCurrentResidue
  sourceAmputatedFieldVertex sourceChargedSecondField

/-- The detector is the original independently amputated four-current restriction. -/
def sourceChargedRead (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (a b : RestStateIndex) :
    (Fin 289→ℂ)→L[ℂ] ℂ :=
  ∑mu : Fin 4,(ContinuousLinearMap.proj (lorentzSlot mu (sourceSpinSlot 2)) : (Fin 289→ℂ)→L[ℂ] ℂ).smulRight
    (sourceAmputatedFieldVertex q pL pR a b (sourceChargedLockedField mu))

theorem sourceChargedRead_original (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (a b : RestStateIndex) (v : Fin 289→ℂ) :
    sourceChargedRead q pL pR a b v=sourceAmputatedFieldVertex q pL pR a b (sourceChargedFieldPart v) := by
  simp only [sourceChargedRead,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,sourceAmputatedFieldVertex,sourceChargedFieldPart,
    sourceChargedCoefficient,Finset.sum_apply,Pi.smul_apply,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

private def fiveLinear : (Fin 5→ℂ)→ₗ[ℂ](Fin 289→ℂ) where
  toFun:=fiveVector
  map_add' x y:=by ext i;by_cases h : i.val<5 <;> simp [fiveVector,h]
  map_smul' z x:=by ext i;by_cases h : i.val<5 <;> simp [fiveVector,h]

def sourceChargedChannel (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 3) : Fin 289→ℂ :=
  sourceChargedNativeFrameJet (fixedMomentum n zeta)*ᵥfiveVector (Pi.single ⟨i.val,by omega⟩ 1)

private theorem three_decomposition (n : PhysicalMomentum) (zeta : ℂ) (f : Fin 289→ℂ) :
    sourceChargedThreeSolution n zeta f=
      ∑i : Fin 3,((sourceChargedDenominator n zeta i)⁻¹*sourceSlowRead f ⟨i.val,by omega⟩) • Pi.single ⟨i.val,by omega⟩ 1 := by
  ext j
  fin_cases j <;> norm_num [sourceChargedThreeSolution,Fin.sum_univ_three,Pi.single_apply] <;> norm_num [Fin.ext_iff]
  exact Or.inl rfl

theorem sourceChargedSecondField_channels (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r : RestStateIndex) :
    sourceChargedSecondField q n zeta.val l r=
      (∑i : Fin 3,((sourceChargedDenominator n zeta.val i)⁻¹*
        sourceSlowRead (sourceActualNativeResidue q n zeta.val l r) ⟨i.val,by omega⟩) • sourceChargedChannel n zeta.val i)+
      sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q n zeta.val l r := by
  unfold sourceChargedSecondField sourceChargedActualFieldJet
  rw [sourceChargedFrameInput_generated q n zeta,three_decomposition]
  have linear (v : Fin 5→ℂ) : fiveVector v=fiveLinear v:=rfl
  simp only [linear,map_sum,map_smul,Matrix.mulVec_sum,Matrix.mulVec_smul]
  rfl

/-- All three denominator channels enter the actual detector, with the regular/contact term retained. -/
theorem sourceChargedSecondResponse_channels (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) :
    sourceChargedRead q pL pR a b (sourceChargedSecondField q n zeta.val l r)=
      (∑i : Fin 3,(sourceChargedDenominator n zeta.val i)⁻¹*
        sourceSlowRead (sourceActualNativeResidue q n zeta.val l r) ⟨i.val,by omega⟩*
          sourceChargedRead q pL pR a b (sourceChargedChannel n zeta.val i))+
      sourceChargedRead q pL pR a b (sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q n zeta.val l r) := by
  rw [sourceChargedSecondField_channels q n zeta]
  simp only [map_add,map_sum,map_smul,smul_eq_mul]

private theorem source_matrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms) := by
  induction terms with
  | nil=>exact continuous_const
  | cons a rest ih=>
    have term : Continuous a.matrix := by
      apply continuous_matrix
      intro i j
      simp only [SourceTerm.matrix,Matrix.single_apply]
      split_ifs
      · unfold Powers.value;fun_prop
      · exact continuous_const
    exact term.add ih

theorem sourceChargedFrame_continuous : Continuous sourceChargedNativeFrameJet := by
  unfold sourceChargedNativeFrameJet sourceLinearPart degreeTensor
  exact (((source_matrix_continuous _).mul continuous_const).sub
    ((((continuous_const.mul continuous_const).mul (source_matrix_continuous _)).mul continuous_const))).mul continuous_const

theorem sourceChargedChannel_continuous (n : PhysicalMomentum) (i : Fin 3) :
    Continuous (fun zeta : ℂ=>sourceChargedChannel n zeta i) := by
  have point : Continuous (fixedMomentum n) := by
    apply continuous_pi
    intro j
    refine Fin.cases ?_ (fun _=>?_) j
    · exact continuous_id
    · exact continuous_const
  exact (sourceChargedFrame_continuous.comp point).matrix_mulVec continuous_const

/-- Pole membership is decided by the actual denominator, not a chosen electromagnetic label. -/
def sourceChargedDenominatorResidue (n : PhysicalMomentum) (c : ℝ) (i : Fin 3) : ℂ :=
  if sourceChargedDenominator n (Complex.I*(c:ℂ)) i=0 then
    ((sourceChargedTemporalCoefficient i:ℂ)*(2*Complex.I*(c:ℂ)))⁻¹ else 0

private theorem denominator_expand (n : PhysicalMomentum) (c eta : ℝ) (i : Fin 3) :
    sourceChargedDenominator n (sourcePoleSide c eta) i=
      sourceChargedDenominator n (Complex.I*(c:ℂ)) i+
        (eta:ℂ)*((sourceChargedTemporalCoefficient i:ℂ)*((eta:ℂ)+2*Complex.I*(c:ℂ))) := by
  unfold sourceChargedDenominator sourcePoleSide
  ring

theorem sourceChargedDenominator_residue (n : PhysicalMomentum) (c : ℝ) (nonzero : c≠0) (i : Fin 3) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)*(sourceChargedDenominator n (sourcePoleSide c eta) i)⁻¹)
      (𝓝[>] 0) (𝓝 (sourceChargedDenominatorResidue n c i)) := by
  have scalar : Tendsto (fun eta : ℝ=>(eta:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  by_cases pole : sourceChargedDenominator n (Complex.I*(c:ℂ)) i=0
  · have coefficient : (sourceChargedTemporalCoefficient i:ℂ)*(2*Complex.I*(c:ℂ))≠0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (sourceChargedTemporalCoefficient_nonzero i))
        (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr nonzero))
    have limit := ((tendsto_const_nhds (x:=(sourceChargedTemporalCoefficient i:ℂ))).mul
      (scalar.add_const (2*Complex.I*(c:ℂ)))).inv₀ (by simpa using coefficient)
    simp only [zero_add] at limit
    rw [sourceChargedDenominatorResidue,if_pos pole]
    apply limit.congr'
    filter_upwards [self_mem_nhdsWithin] with eta positive
    rw [denominator_expand,pole,zero_add,mul_inv_rev]
    have hn : (eta:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
    field_simp
  · have continuous : Continuous (fun eta : ℝ=>sourceChargedDenominator n (sourcePoleSide c eta) i) := by
      unfold sourceChargedDenominator sourcePoleSide
      fun_prop
    have inverse := (continuous.tendsto 0).inv₀ (by simpa [sourcePoleSide] using pole)
    have limit:=scalar.mul (inverse.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0))
    simpa only [sourceChargedDenominatorResidue,if_neg pole,zero_mul] using limit

theorem sourceSlowRead_continuous : Continuous sourceSlowRead := by
  apply continuous_pi
  intro i
  unfold sourceSlowRead
  split_ifs
  · exact (continuous_apply (fiveIndex i)).comp (continuous_const.matrix_mulVec continuous_id)
  · exact continuous_const

theorem sourceSlowRead_smul (z : ℂ) (f : Fin 289→ℂ) : sourceSlowRead (z • f)=z • sourceSlowRead f := by
  ext i
  by_cases h : i.val<3 <;> simp [sourceSlowRead,h,Matrix.mulVec_smul]

/-- The original retainer numerator and three physical field poles share this generated boundary field. -/
def sourceChargedBoundaryField (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  ∑i : Fin 3,(sourceChargedDenominatorResidue n c i*
    sourceSlowRead (sourceNativeBoundaryResidue q n c l r) ⟨i.val,by omega⟩) •
      sourceChargedChannel n (Complex.I*(c:ℂ)) i

/-- The third field denominator survives until the actual source/detector residue decides its contribution. -/
theorem sourceChargedSecondField_boundary (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ)
    (nonzero : c≠0) (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>((eta:ℂ)^3) • sourceChargedSecondField q n (sourcePoleSide c eta) l r)
      (𝓝[>] 0) (𝓝 (sourceChargedBoundaryField q n c l r)) := by
  have scalar : Tendsto (fun eta : ℝ=>(eta:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have side : Tendsto (sourcePoleSide c) (𝓝[>] 0) (𝓝 (Complex.I*(c:ℂ))) := by
    change Tendsto (fun eta : ℝ=>(eta:ℂ)+Complex.I*(c:ℂ)) _ _
    simpa only [zero_add] using scalar.add_const (Complex.I*(c:ℂ))
  have slow := sourceSlowRead_continuous.continuousAt.tendsto.comp
    ((sourceNativeBoundaryNumerator_limit q n c l r).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0))
  have channel (i : Fin 3) := ((sourceChargedDenominator_residue n c nonzero i).mul
    (slow.apply_nhds ⟨i.val,by omega⟩)).smul
      ((sourceChargedChannel_continuous n i).continuousAt.tendsto.comp side)
  have current : Tendsto (fun eta : ℝ=>sourceRegularMatrix 0*ᵥsourceWholeCurrentNumerator q n c eta l r)
      (𝓝[>] 0) (𝓝 (sourceRegularMatrix 0*ᵥsourceWholeCurrentNumerator q n c 0 l r)) :=
    (continuous_const.matrix_mulVec continuous_id).continuousAt.tendsto.comp
      ((sourceWholeCurrentNumerator_limit q n c l r).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0))
  have regular := scalar.smul (show Tendsto
    (fun eta : ℝ=>sourceRegularMatrix 0*ᵥsourceWholeCurrentNumerator q n c eta l r)
      (𝓝[>] 0) (𝓝 (sourceRegularMatrix 0*ᵥsourceWholeCurrentNumerator q n c 0 l r)) from current)
  have total := (tendsto_finsetSum Finset.univ (fun i _=>channel i)).add regular
  simp only [zero_smul,add_zero] at total
  apply total.congr'
  filter_upwards [self_mem_nhdsWithin] with eta positive
  have legal : sourcePoleSide c eta∈sourceCausalDomain n:=sourcePoleSide_field_domain n c eta nonzero positive
  simp only [Function.comp_def]
  rw [sourceChargedSecondField_channels q n ⟨sourcePoleSide c eta,legal⟩,
    ←sourceNativeBoundaryNumerator_generated q n c eta positive l r,
    ←sourceWholeCurrentNumerator_generated q n c eta positive l r,sourceSlowRead_smul]
  simp only [Finset.smul_sum,smul_add,Matrix.mulVec_smul,smul_smul,Pi.smul_apply,smul_eq_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  · congr 1
    ring

def sourceChargedBoundaryResponse (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) : ℂ :=
  sourceChargedRead q pL pR a b (sourceChargedBoundaryField q n c l r)

theorem sourceChargedSecondResponse_boundary (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ)
    (nonzero : c≠0) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)^3*sourceChargedSecondResponse q c eta l r a b pL pR n)
      (𝓝[>] 0) (𝓝 (sourceChargedBoundaryResponse q n c l r a b pL pR)) := by
  have result := (sourceChargedRead q pL pR a b).continuous.continuousAt.tendsto.comp
    (sourceChargedSecondField_boundary q n c nonzero l r)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,sourceChargedRead_original,
    sourceChargedSecondResponse,sourceChargedBoundaryResponse] using result

end LowEnergy.PreparationVacuumChargedLongRangeRead
