import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarFlatJoint
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceHamiltonianVolume
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarNativeComparison
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert
open GaussLiveMomentum GaussNativeEnergy SourceCoframeVolume SourceHamiltonianVolume
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceScalarFlatJoint
open scoped ContDiff InnerProductSpace BigOperators

private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul

private def momentumRow (f : QuantumTest) : Scalar →ₗ[ℝ] H where
  toFun v := embed (covariantMomentum (v,0) f)
  map_add' v w := by
    rw [←map_add]
    apply congrArg embed
    apply DFunLike.ext
    intro z
    change covariantMomentum (v+w,0) f z=covariantMomentum (v,0) f z+covariantMomentum (w,0) f z
    rw [covariantMomentum_apply,covariantMomentum_apply,covariantMomentum_apply]
    have hvw : (v+w,(0 : Gauge))=(v,0)+(w,0) := by simp
    rw [hvw,map_add]
    simp only [Prod.fst_add,Prod.snd_add,map_add,add_apply]
    have hd : (0,(inverseL z (v,0)).2+(inverseL z (w,0)).2)=
        ((0,(inverseL z (v,0)).2) : SourceCoordinateSlice)+(0,(inverseL z (w,0)).2) := by simp
    rw [hd,map_add]
    change (-Complex.I) • (_+_+(_+_))=(-Complex.I) • (_+_)+(-Complex.I) • (_+_)
    simp only [smul_add]
    abel
  map_smul' c v := by
    rw [←LinearMap.map_smul_of_tower]
    apply congrArg embed
    apply DFunLike.ext
    intro z
    change covariantMomentum (c • v,0) f z=c • covariantMomentum (v,0) f z
    rw [covariantMomentum_apply,covariantMomentum_apply]
    have hcv : (c • v,(0 : Gauge))=c • (v,0) := by simp
    rw [hcv,map_smul]
    simp only [Prod.smul_fst,Prod.smul_snd,map_smul,smul_apply]
    have hd : (0,c • (inverseL z (v,0)).2)=
        c • ((0,(inverseL z (v,0)).2) : SourceCoordinateSlice) := by simp
    rw [hd,map_smul,←smul_add,smul_comm]

private theorem momentumRow_apply (f : QuantumTest) (v : Scalar) :
    momentumRow f v=embed (covariantMomentum (v,0) f) := rfl

private theorem basis_energy {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) (T : E →ₗ[ℝ] V) :
    (∑ i,‖T (b i)‖^2)=∑ j,‖T (c j)‖^2 := by
  have ht (x : E) : (∑ j,(inner ℝ (c j) x) • T (c j))=T x := by
    simpa only [map_sum,map_smul] using congrArg T (c.sum_repr' x)
  have hu (x : E) : (∑ i,(inner ℝ (b i) x) • T (b i))=T x := by
    simpa only [map_sum,map_smul] using congrArg T (b.sum_repr' x)
  simp_rw [←real_inner_self_eq_norm_sq]
  calc
    _ = ∑ i,∑ j,(inner ℝ (c j) (b i))*inner ℝ (T (c j)) (T (b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      nth_rw 1 [←ht (b i)]
      simp only [sum_inner,real_inner_smul_left]
    _ = ∑ j,∑ i,(inner ℝ (c j) (b i))*inner ℝ (T (c j)) (T (b i)) := Finset.sum_comm
    _ = ∑ j,inner ℝ (T (c j)) (T (c j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [←hu (c j)]
      simp only [inner_sum,real_inner_smul_right]
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_comm (c j) (b i)]

abbrev OrthogonalIndex := Fin (Module.finrank ℝ scalarSliceᗮ)
def orthogonalFrame : OrthonormalBasis OrthogonalIndex ℝ scalarSliceᗮ :=
  stdOrthonormalBasis ℝ scalarSliceᗮ
private def ambientFrame : OrthonormalBasis (SliceIndex ⊕ OrthogonalIndex) ℝ Scalar :=
  (scalarFrame.prod orthogonalFrame).map scalarSlice.orthogonalDecomposition.symm

private theorem ambientFrame_left (i : SliceIndex) : ambientFrame (Sum.inl i)=(scalarFrame i : Scalar) := by
  simp [ambientFrame,Submodule.orthogonalDecomposition_symm_apply]
private theorem ambientFrame_right (i : OrthogonalIndex) : ambientFrame (Sum.inr i)=(orthogonalFrame i : Scalar) := by
  simp [ambientFrame,Submodule.orthogonalDecomposition_symm_apply]

def nativeScalarEnergy (f : QuantumTest) : ℝ :=
  ∑ a : ScalarIndex,‖embed (covariantMomentum (scalarDirection a) f)‖^2

def orthogonalEnergy (f : QuantumTest) : ℝ :=
  ∑ a : OrthogonalIndex,‖embed (covariantMomentum ((orthogonalFrame a : Scalar),0) f)‖^2

/-- Full native scalar energy includes the exact flat61 energy and all nine orthogonal rows. -/
theorem actual_scalar_energy_split (f : QuantumTest) :
    nativeScalarEnergy f=(sourcePair f (flatKinetic f)).re+orthogonalEnergy f := by
  have h := basis_energy scalarBasis ambientFrame (momentumRow f)
  rw [Fintype.sum_sum_type] at h
  simp only [ambientFrame_left,ambientFrame_right] at h
  rw [actual_flat_kinetic_square]
  simp only [momentumRow_apply] at h
  have hs : (∑ i : SliceIndex,‖embed (covariantMomentum ((scalarFrame i : Scalar),0) f)‖^2)=
      ∑ i : SliceIndex,‖embed (flatMomentum (scalarFrame i) f)‖^2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [actual_flat_momentum]
  rw [hs] at h
  exact h

theorem actual_orthogonal_frame_dimension : Fintype.card OrthogonalIndex=9 := by
  have h := scalarSlice.finrank_add_finrank_orthogonal
  rw [SourceQuantumScalarOrbitDimensions.scalarSlice_finrank,
    SourceQuantumNativeDimensions.scalar_finrank] at h
  simpa only [OrthogonalIndex,Fintype.card_fin] using (show Module.finrank ℝ scalarSliceᗮ=9 by omega)

private theorem volume_weight (f : QuantumTest) :
    volumeAction (multiply scalarWeight scalarWeight_smooth f)=(-sourceTime 0 : ℂ) • f := by
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · change (volume z : ℂ) • ((scalarWeight z : ℂ) • f z)=(-sourceTime 0 : ℂ) • f z
    rw [smul_smul]
    apply congrArg (fun c : ℂ => c • f z)
    rw [scalarWeight]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (volume_pos ⟨z,hz⟩).ne']
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    change (volume z : ℂ) • ((scalarWeight z : ℂ) • f z)=(-sourceTime 0 : ℂ) • f z
    rw [hf,smul_zero,smul_zero,smul_zero]

private theorem volume_sandwich (v : Ambient) (f : QuantumTest) :
    sourcePair f (volumeAction (sandwich v v scalarWeight scalarWeight_smooth f))=
      (-sourceTime 0 : ℂ)*sourcePair (covariantMomentum v f) (covariantMomentum v f) := by
  have hc := LinearMap.congr_fun (native_adjoint_volume v).eq
    (multiply scalarWeight scalarWeight_smooth (covariantMomentum v f))
  change sourcePair f (volumeAction (GaussMomentumAdjoint.adjoint v
    (multiply scalarWeight scalarWeight_smooth (covariantMomentum v f))))=_
  change GaussMomentumAdjoint.adjoint v (volumeAction _) =
    volumeAction (GaussMomentumAdjoint.adjoint v _) at hc
  rw [←hc,volume_weight,adjoint_pair]
  simp only [sourcePair,map_smul,inner_smul_right]

/-- The source sign is w=-n/U, so the full scalar momentum Gram is a negative kinetic form. -/
theorem actual_native_scalar_form (f : QuantumTest) :
    (sourcePair f (volumeAction (scalarKinetic f))).re=
      -(sourceTime 0/2)*nativeScalarEnergy f := by
  have h : sourcePair f (volumeAction (scalarKinetic f))=
      (1/2 : ℂ)*∑ a : ScalarIndex,(-sourceTime 0 : ℂ)*
        sourcePair (covariantMomentum (scalarDirection a) f) (covariantMomentum (scalarDirection a) f) := by
    simp only [scalarKinetic,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum]
    change inner ℂ (embed f) (embed ((1/2 : ℂ) • _))=_
    rw [map_smul,inner_smul_right]
    congr 1
    change sourcePair f (∑ a : ScalarIndex,volumeAction _) = _
    simp only [sourcePair,map_sum,inner_sum]
    exact Finset.sum_congr rfl (fun a _ => volume_sandwich (scalarDirection a) f)
  rw [h]
  have hi (a : ScalarIndex) : sourcePair (covariantMomentum (scalarDirection a) f)
      (covariantMomentum (scalarDirection a) f)=(‖embed (covariantMomentum (scalarDirection a) f)‖^2 : ℂ) := by
    simpa only [sourcePair] using! inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed (covariantMomentum (scalarDirection a) f))
  simp only [hi,←Finset.mul_sum]
  change ((1/2 : ℂ)*((-sourceTime 0 : ℂ)*∑ a : ScalarIndex,
    (‖embed (covariantMomentum (scalarDirection a) f)‖^2 : ℂ))).re=_
  have he : (∑ a : ScalarIndex,(‖embed (covariantMomentum (scalarDirection a) f)‖^2 : ℂ))=
      (nativeScalarEnergy f : ℂ) := by
    simp only [nativeScalarEnergy,Complex.ofReal_sum,Complex.ofReal_pow]
  rw [he]
  simp only [Complex.mul_re,Complex.div_re,Complex.one_re,Complex.one_im,
    Complex.re_ofNat,Complex.im_ofNat,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_re,Complex.neg_im,mul_zero,sub_zero,neg_zero]
  norm_num
  ring

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

theorem actual_flat_native_comparison (f : QuantumTest) :
    (sourcePair f (flatKinetic f)).re≤
      -(2/sourceTime 0)*(sourcePair f (volumeAction (scalarKinetic f))).re := by
  rw [actual_native_scalar_form]
  have he : -(2/sourceTime 0)*(-(sourceTime 0/2)*nativeScalarEnergy f)=nativeScalarEnergy f := by
    field_simp [lapse_pos.ne']
  rw [he,actual_scalar_energy_split]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Direct CAR-current consumer of the actual full scalar kinetic sign. -/
theorem actual_flat_current_native_bound (sharp : Bool) (f : QuantumTest) :
    ‖embed (flatScalarCurrent sharp f)‖^2≤rowCost sharp*
      (-(2/sourceTime 0)*(sourcePair f (volumeAction (scalarKinetic f))).re) := by
  exact (actual_flat_current_bound sharp f).trans
    (mul_le_mul_of_nonneg_left (actual_flat_native_comparison f)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end LowEnergy.SourceScalarNativeComparison
