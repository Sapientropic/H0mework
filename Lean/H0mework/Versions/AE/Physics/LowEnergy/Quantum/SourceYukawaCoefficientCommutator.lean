import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeNeutralSpinCurrent
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.GaussYukawaGrade

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceYukawaCoefficientCommutator
open SaturationMonoid.PhysicsCore
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open GaussMatterCore SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarGaugeForce
open SourceInverseNeutralSpinCurrent SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge GaussYukawaCoefficient
open GaussLiveMomentum
open scoped ContDiff InnerProductSpace Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private def side (sharp : Bool) (i : Mode) : Prop :=
  if sharp then i ∉ SourceQuantumFockGrade56.target else i ∈ SourceQuantumFockGrade56.target

private def oneBlock (sharp : Bool) (A : Matrix Mode Mode ℂ) : Prop :=
  (∀ i j, ¬side sharp i → A i j=0) ∧ (∀ i j, side sharp j → A i j=0)

private theorem original_matrix_zero (phi : Scalar) (i j : Mode)
    (hij : i ∉ SourceQuantumFockGrade56.target ∨ j ∈ SourceQuantumFockGrade56.target) :
    fullMatrix phi i j=0 := by
  have h := GaussYukawaGrade.matrix_raises phi i j
  by_cases hi : i ∈ SourceQuantumFockGrade56.target <;>
    by_cases hj : j ∈ SourceQuantumFockGrade56.target
  · simpa [hi,hj] using h
  · exact (hij.elim (fun hn => hn hi) (fun hp => hj hp)).elim
  · norm_num [hi,hj] at h
    exact h
  · simpa [hi,hj] using h

private theorem branch_block (sharp : Bool) (phi : Scalar) : oneBlock sharp (branchMatrix sharp phi) := by
  cases sharp
  · constructor
    · intro i j hi
      exact original_matrix_zero phi i j (Or.inl hi)
    · intro i j hj
      exact original_matrix_zero phi i j (Or.inr hj)
  · constructor
    · intro i j hi
      have hi' : i ∈ SourceQuantumFockGrade56.target := by simpa [side] using hi
      change star (fullMatrix phi j i)=0
      rw [original_matrix_zero phi j i (Or.inr hi'),star_zero]
    · intro i j hj
      have hj' : j ∉ SourceQuantumFockGrade56.target := by simpa [side] using hj
      change star (fullMatrix phi j i)=0
      rw [original_matrix_zero phi j i (Or.inl hj'),star_zero]

private theorem same_block_product {sharp : Bool} {A B : Matrix Mode Mode ℂ}
    (hA : oneBlock sharp A) (hB : oneBlock sharp B) : A*B=0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : side sharp k
  · rw [hA.2 i k hk,zero_mul]
  · rw [hB.1 k j hk,mul_zero]

private theorem preserving_cross {sharp : Bool} {A : Matrix Mode Mode ℂ}
    (hA : GaussFockLabel.Preserves A) (i j : Mode) (hij : ¬(side sharp i ↔ side sharp j)) :
    A i j=0 := by
  have h := hA i j
  cases sharp <;> by_cases hi : i ∈ SourceQuantumFockGrade56.target <;>
    by_cases hj : j ∈ SourceQuantumFockGrade56.target <;>
    simp [side,hi,hj] at hij <;> simpa [GaussFockLabel.charge,hi,hj] using h

private theorem preserving_left {sharp : Bool} {A B : Matrix Mode Mode ℂ}
    (hA : GaussFockLabel.Preserves A) (hB : oneBlock sharp B) : oneBlock sharp (A*B) := by
  constructor
  · intro i j hi
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : side sharp k
    · rw [preserving_cross hA i k (by tauto),zero_mul]
    · rw [hB.1 k j hk,mul_zero]
  · intro i j hj
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [hB.2 k j hj,mul_zero]

private theorem preserving_right {sharp : Bool} {A B : Matrix Mode Mode ℂ}
    (hA : oneBlock sharp A) (hB : GaussFockLabel.Preserves B) : oneBlock sharp (A*B) := by
  constructor
  · intro i j hi
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [hA.1 i k hi,zero_mul]
  · intro i j hj
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : side sharp k
    · rw [hA.2 i k hk,zero_mul]
    · rw [preserving_cross hB k j (by tauto),mul_zero]

private theorem preserving_bracket {sharp : Bool} {A B : Matrix Mode Mode ℂ}
    (hA : GaussFockLabel.Preserves A) (hB : oneBlock sharp B) : oneBlock sharp (bracket A B) := by
  have hl := preserving_left hA hB
  have hr := preserving_right hB hA
  constructor
  · intro i j hi
    simp only [bracket,Matrix.sub_apply,hl.1 i j hi,hr.1 i j hi,sub_self]
  · intro i j hj
    simp only [bracket,Matrix.sub_apply,hl.2 i j hj,hr.2 i j hj,sub_self]

private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    bracket (quantized A) (quantized B)=quantized (bracket A B) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [bracket,quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)

private theorem quantized_adjoint (A : Matrix Mode Mode ℂ) :
    (quantized A).adjoint=quantized A.conjTranspose := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact SourceQuantumFockGauge.quantizedFiber_adjoint A g f

private theorem branch_quantized (sharp : Bool) (phi : Scalar) :
    branchMap sharp phi=quantized (branchMatrix sharp phi) := by
  cases sharp
  · rfl
  · change (sourceMap phi).adjoint=quantized (fullMatrix phi).conjTranspose
    change (quantized (fullMatrix phi)).adjoint=quantized (fullMatrix phi).conjTranspose
    exact quantized_adjoint _

private theorem quantized_zero : quantized (0 : Matrix Mode Mode ℂ)=0 := map_zero quantizer

private theorem blocks_quantized_commute {sharp : Bool} {A B : Matrix Mode Mode ℂ}
    (hA : oneBlock sharp A) (hB : oneBlock sharp B) : Commute (quantized A) (quantized B) := by
  apply sub_eq_zero.mp
  change bracket (quantized A) (quantized B)=0
  rw [quantized_bracket]
  simp only [bracket,same_block_product hA hB,same_block_product hB hA,sub_self,quantized_zero]

private theorem full_at (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    fullAction sharp f z=branchMap sharp (scalarField z) (f z) := by
  cases sharp <;> rfl

private theorem spin_at (j : Fin 4) (f : QuantumTest) (z : SourceCoordinateSlice) :
    activeSpin j f z=quantized (GaussCoframeSpin.full (activeIndex j)) (f z) := rfl

/-- Same-branch coefficient commutation follows from the original one-particle block and full CAR. -/
theorem fullY_constant_commute (sharp : Bool) (v : Scalar) :
    Commute (fullAction sharp) (constantAction sharp v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change fullAction sharp (constantAction sharp v f) z=constantAction sharp v (fullAction sharp f) z
  rw [full_at]
  change branchMap sharp (scalarField z) (branchMap sharp v (f z))=
    branchMap sharp v (fullAction sharp f z)
  rw [full_at,branch_quantized,branch_quantized]
  exact congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z))
    (blocks_quantized_commute (branch_block sharp _) (branch_block sharp _)).eq

/-- The actual boost/chiral variation remains the same oriented block after quantization. -/
theorem fullY_spinVariation_commute (sharp : Bool) (j : Fin 4) :
    Commute (fullAction sharp) (spinVariation sharp j) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have h := (blocks_quantized_commute (branch_block sharp (scalarField z))
    (preserving_bracket (GaussFockLabel.spin_preserves (activeIndex j))
      (branch_block sharp (scalarField z)))).eq
  rw [←branch_quantized,←original_active_spin_matrix] at h
  have hf := congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z)) h
  simpa only [spinVariation,bracket,LinearMap.sub_apply,Module.End.mul_apply,
    sub_apply,map_sub,full_at,spin_at,mul_apply_eq_comp] using hf

private theorem matter_at (f : QuantumTest) (z : SourceCoordinateSlice) :
    matterAction f z=∑ i : Fin 3,∑ b : Fin 3,quantized (localMatrix i b z) (f z) := by
  simp only [matterAction,LinearMap.sum_apply,sum_apply]
  rfl

private theorem matter_double_at (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    bracket (bracket matterAction (fullAction sharp)) (fullAction sharp) f z=0 := by
  have hz (i b : Fin 3) :
      bracket (bracket (quantized (localMatrix i b z)) (branchMap sharp (scalarField z)))
        (branchMap sharp (scalarField z))=0 := by
    rw [branch_quantized,quantized_bracket]
    exact sub_eq_zero.mpr (blocks_quantized_commute
      (preserving_bracket (GaussFockLabel.matter_preserves i b z) (branch_block sharp _))
      (branch_block sharp _)).eq
  have hz' (i b : Fin 3) := congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z)) (hz i b)
  simp only [bracket,mul_apply_eq_comp,sub_apply,map_sub,zero_apply] at hz'
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,sub_apply,map_sub,full_at,matter_at,
    map_sum]
  simp only [←Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro b _
  exact hz' i b

/-- The original spatial matter action has vanishing second right Yukawa derivative. -/
theorem matter_current_Y_zero (sharp : Bool) :
    bracket (bracket matterAction (fullAction sharp)) (fullAction sharp)=0 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact matter_double_at sharp f z

private theorem pair_smul_right (f g : QuantumTest) (c : ℂ) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]

private theorem full_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (fullAction sharp g)=sourcePair (fullAction (!sharp) f) g := by
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair g f)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair f g

/-- The original density adjoint generates the same full coefficient current as native momentum. -/
theorem native_full_adjoint_commutator (sharp : Bool) (v : Ambient) :
    bracket (GaussMomentumAdjoint.adjoint v) (fullAction sharp)=
      (-Complex.I) • constantAction sharp v.1 := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  have h := SourceScalarGaugeForce.original_full_momentum (!sharp) v f
  have hh := congrArg (fun t : QuantumTest => sourcePair t g) h
  simp only [sourcePair,map_add,map_smul,inner_add_left,inner_smul_left,map_neg,Complex.conj_I,neg_neg] at hh
  change sourcePair f (GaussMomentumAdjoint.adjoint v (fullAction sharp g)-
    fullAction sharp (GaussMomentumAdjoint.adjoint v g))=
      sourcePair f ((-Complex.I) • constantAction sharp v.1 g)
  have hl : sourcePair f (GaussMomentumAdjoint.adjoint v (fullAction sharp g)-
      fullAction sharp (GaussMomentumAdjoint.adjoint v g))=
      sourcePair (fullAction (!sharp) (covariantMomentum v f)) g-
        sourcePair (covariantMomentum v (fullAction (!sharp) f)) g := by
    change inner ℂ (embed f) (embed (_-_))=_
    rw [map_sub,inner_sub_right]
    change sourcePair f (GaussMomentumAdjoint.adjoint v (fullAction sharp g))-
      sourcePair f (fullAction sharp (GaussMomentumAdjoint.adjoint v g))=_
    rw [GaussNativeForm.adjoint_pair,full_pair,full_pair,GaussNativeForm.adjoint_pair]
  rw [hl,pair_smul_right,SourceMixedNativeReturn.constant_pair]
  change inner ℂ (embed (fullAction (!sharp) (covariantMomentum v f))) (embed g)-
    inner ℂ (embed (covariantMomentum v (fullAction (!sharp) f))) (embed g)=
      (-Complex.I)*inner ℂ (embed (constantAction (!sharp) v.1 f)) (embed g)
  linear_combination -hh

end LowEnergy.SourceYukawaCoefficientCommutator
