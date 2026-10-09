import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedPropagatingRead

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumChargedLongRangeRead
open PreparationVacuumChargedSpatialResponse PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumObservedPoleTensor
open PreparationVacuumObservedStaticResidue PreparationVacuumStaticSimpleCoupling
open PreparationVacuumQuantumSlowResidue PreparationVacuumFullSlowFieldResponse
open PreparationVacuumWholeOrigin PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFullOriginResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationVacuumCausalPoleResponse CanonicalGradedSpatialSource Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] sourceChargedNativeFrameJet sourceActualNativeResidue sourceFullCurrentResidue
  sourceStaticCurrent sourceStaticNative sourceNativeSimple sourceCurrentSimple sourceChargedSecondField

private theorem linear_power (a : Powers) (degree : a.total=1) (p q : Fin 4→ℂ) (z : ℂ) :
    a.value (p+z • q)=a.value p+z*a.value q := by
  rcases a with ⟨t,x,y,w⟩
  simp only [Powers.total] at degree
  have cases : (t=1∧x=0∧y=0∧w=0)∨(t=0∧x=1∧y=0∧w=0)∨
      (t=0∧x=0∧y=1∧w=0)∨(t=0∧x=0∧y=0∧w=1) := by omega
  rcases cases with h|h|h|h <;> rcases h with ⟨rfl,rfl,rfl,rfl⟩ <;> simp [Powers.value]

private theorem linear_matrix (terms : List SourceTerm) (degree : ∀a∈terms,a.powers.total=1)
    (p q : Fin 4→ℂ) (z : ℂ) : sourceMatrix terms (p+z • q)=sourceMatrix terms p+z • sourceMatrix terms q := by
  induction terms with
  | nil=>simp [sourceMatrix]
  | cons a rest ih=>
    have first : a.matrix (p+z • q)=a.matrix p+z • a.matrix q := by
      ext i j
      simp only [SourceTerm.matrix,Matrix.add_apply,Matrix.smul_apply,Matrix.single_apply]
      split_ifs <;> simp only [smul_eq_mul,linear_power a.powers (degree a (by simp)),mul_add] <;> ring
    rw [sourceMatrix_cons,sourceMatrix_cons,sourceMatrix_cons,first,ih (fun b hb=>degree b (by simp [hb]))]
    module

private theorem linear_part (terms : List SourceTerm) (p q : Fin 4→ℂ) (z : ℂ) :
    sourceLinearPart terms (p+z • q)=sourceLinearPart terms p+z • sourceLinearPart terms q := by
  apply linear_matrix
  intro a member
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- The time jet is retained alongside the spatial first jet. -/
theorem sourceChargedChannel_static_split (n : PhysicalMomentum) (eta : ℂ) (i : Fin 3) :
    sourceChargedChannel n eta i=sourceChargedChannel n 0 i+eta • sourceChargedChannel 0 1 i := by
  have point : fixedMomentum n eta=fixedMomentum n 0+eta • fixedMomentum 0 1 := by
    ext j
    refine Fin.cases ?_ (fun _=>?_) j
    · simp [fixedMomentum,fullMomentum]
    · simp [fixedMomentum,fullMomentum,physicalSpatial]
  simp only [sourceChargedChannel,point,sourceChargedNativeFrameJet,linear_part,
    mul_add,add_mul,sub_mul,mul_smul_comm,smul_mul_assoc,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec]
  module

theorem sourceChargedStaticDenominator_nonzero (n : PhysicalMomentum) (spatial : 0<spatialSquare n) (i : Fin 3) :
    sourceChargedDenominator n 0 i≠0 := by
  simp only [sourceChargedDenominator,zero_pow (by decide : 2≠0),mul_zero,add_zero]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (sourceChargedSpatialCoefficient_positive i).ne')
    (Complex.ofReal_ne_zero.mpr spatial.ne')

theorem sourceChargedStaticInverse_limit (n : PhysicalMomentum) (spatial : 0<spatialSquare n) (i : Fin 3) :
    Tendsto (fun eta : ℝ=>(sourceChargedDenominator n (eta:ℂ) i)⁻¹)
      (𝓝[>] 0) (𝓝 ((sourceChargedDenominator n 0 i)⁻¹)) := by
  have continuous : Continuous (fun eta : ℝ=>sourceChargedDenominator n (eta:ℂ) i) := by
    unfold sourceChargedDenominator
    fun_prop
  exact (continuous.continuousAt.tendsto.inv₀ (by simpa using sourceChargedStaticDenominator_nonzero n spatial i)).mono_left nhdsWithin_le_nhds

/-- The exact quadratic denominator error pays the change from causal damping to the static inverse. -/
theorem sourceChargedStaticInverse_error (n : PhysicalMomentum) (spatial : 0<spatialSquare n)
    (eta : ℂ) (i : Fin 3) (legal : sourceChargedDenominator n eta i≠0) :
    (sourceChargedDenominator n eta i)⁻¹-(sourceChargedDenominator n 0 i)⁻¹=
      -((sourceChargedTemporalCoefficient i:ℂ)*eta^2)/
        (sourceChargedDenominator n 0 i*sourceChargedDenominator n eta i) := by
  have static:=sourceChargedStaticDenominator_nonzero n spatial i
  have difference : sourceChargedDenominator n eta i=sourceChargedDenominator n 0 i+
      (sourceChargedTemporalCoefficient i:ℂ)*eta^2 := by simp [sourceChargedDenominator]
  field_simp
  rw [difference]
  ring

theorem sourceChargedStaticInverse_slope (n : PhysicalMomentum) (spatial : 0<spatialSquare n) (i : Fin 3) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)⁻¹*((sourceChargedDenominator n (eta:ℂ) i)⁻¹-
      (sourceChargedDenominator n 0 i)⁻¹)) (𝓝[>] 0) (𝓝 0) := by
  have scalar : Tendsto (fun eta : ℝ=>(eta:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have base := (((tendsto_const_nhds (x:= -(sourceChargedTemporalCoefficient i:ℂ))).mul scalar).mul_const
    ((sourceChargedDenominator n 0 i)⁻¹)).mul (sourceChargedStaticInverse_limit n spatial i)
  simp only [mul_zero,zero_mul] at base
  apply base.congr'
  have continuous : Continuous (fun eta : ℝ=>sourceChargedDenominator n (eta:ℂ) i) := by
    unfold sourceChargedDenominator
    fun_prop
  have legal : ∀ᶠ eta : ℝ in 𝓝[>] 0,sourceChargedDenominator n (eta:ℂ) i≠0 :=
    (continuous.continuousAt.eventually_ne (by simpa using sourceChargedStaticDenominator_nonzero n spatial i)).filter_mono nhdsWithin_le_nhds
  filter_upwards [legal,self_mem_nhdsWithin] with eta valid positive
  rw [sourceChargedStaticInverse_error n spatial (eta:ℂ) i valid]
  have nz : (eta:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  field_simp

/-- The actual charged second-order field's static double coefficient includes the full contact return. -/
def sourceChargedStaticDouble (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) : Fin 289→ℂ :=
  (∑i : Fin 3,((sourceChargedDenominator n 0 i)⁻¹*
    sourceSlowRead (sourceStaticNative q n l r) ⟨i.val,by omega⟩) • sourceChargedChannel n 0 i)+
    sourceRegularMatrix 0*ᵥsourceStaticCurrent q n l r

def sourceChargedStaticSimple (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) : Fin 289→ℂ :=
  (∑i : Fin 3, (((sourceChargedDenominator n 0 i)⁻¹*
    sourceSlowRead (sourceNativeSimple q n l r) ⟨i.val,by omega⟩) • sourceChargedChannel n 0 i+
    ((sourceChargedDenominator n 0 i)⁻¹*sourceSlowRead (sourceStaticNative q n l r) ⟨i.val,by omega⟩) •
      sourceChargedChannel 0 1 i))+sourceRegularMatrix 0*ᵥsourceCurrentSimple q n l r

theorem sourceChargedStaticDouble_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (spatial : 0<spatialSquare n) (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>((eta:ℂ)^2) • sourceChargedSecondField q n (eta:ℂ) l r)
      (𝓝[>] 0) (𝓝 (sourceChargedStaticDouble q n l r)) := by
  have scalar : Tendsto (fun eta : ℝ=>(eta:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have slow := sourceStaticSlow_generated q n l r
  have channels (i : Fin 3) := ((sourceChargedStaticInverse_limit n spatial i).mul
    (slow.apply_nhds ⟨i.val,by omega⟩)).smul
      ((sourceChargedChannel_continuous n i).continuousAt.tendsto.comp scalar)
  have regular : Tendsto (fun eta : ℝ=>sourceRegularMatrix 0*ᵥ(((eta:ℂ)^2) • sourceFullCurrentResidue q n (eta:ℂ) l r))
      (𝓝[>] 0) (𝓝 (sourceRegularMatrix 0*ᵥsourceStaticCurrent q n l r)) :=
    (continuous_const.matrix_mulVec continuous_id).continuousAt.tendsto.comp (sourceStaticCurrent_generated q n l r)
  have total := (tendsto_finsetSum Finset.univ (fun i _=>channels i)).add
    (show Tendsto (fun eta : ℝ=>sourceRegularMatrix 0*ᵥ(((eta:ℂ)^2) • sourceFullCurrentResidue q n (eta:ℂ) l r))
      (𝓝[>] 0) (𝓝 (sourceRegularMatrix 0*ᵥsourceStaticCurrent q n l r)) from regular)
  apply total.congr'
  filter_upwards [sourceStatic_causal_eventually n spatial] with eta legal
  rw [sourceChargedSecondField_channels q n ⟨(eta:ℂ),legal⟩]
  simp only [smul_add,Finset.smul_sum,smul_smul,Pi.smul_apply,smul_eq_mul,Matrix.mulVec_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

private theorem laurent_channel (z D D0 x x2 : ℂ) (nonzero : z≠0) (u v : Fin 289→ℂ) :
    z • ((D*x) • (u+z • v)-(z⁻¹)^2 • ((D0*x2) • u))=
      (D*(z*(x-(z⁻¹)^2*x2))) • (u+z • v)+(D*x2) • v+(z⁻¹*(D-D0)*x2) • u := by
  ext j
  simp only [Pi.smul_apply,Pi.add_apply,Pi.sub_apply,smul_eq_mul]
  field_simp
  ring

/-- Both retainer cross terms, the true time jet and complete regular return generate the static simple coefficient. -/
theorem sourceChargedStaticSimple_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (spatial : 0<spatialSquare n) (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>(eta:ℂ) • (sourceChargedSecondField q n (eta:ℂ) l r-
      ((eta:ℂ)⁻¹)^2 • sourceChargedStaticDouble q n l r))
      (𝓝[>] 0) (𝓝 (sourceChargedStaticSimple q n l r)) := by
  have scalar : Tendsto (fun eta : ℝ=>(eta:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have slow := sourceSlow_simple_generated q n l r
  have term (i : Fin 3) := (((sourceChargedStaticInverse_limit n spatial i).mul
    (slow.apply_nhds ⟨i.val,by omega⟩)).smul
      ((sourceChargedChannel_continuous n i).continuousAt.tendsto.comp scalar)).add
    (((sourceChargedStaticInverse_limit n spatial i).mul_const
      (sourceSlowRead (sourceStaticNative q n l r) ⟨i.val,by omega⟩)).smul_const (sourceChargedChannel 0 1 i)) |>.add
    (((sourceChargedStaticInverse_slope n spatial i).mul_const
      (sourceSlowRead (sourceStaticNative q n l r) ⟨i.val,by omega⟩)).smul_const (sourceChargedChannel n 0 i))
  have regular : Tendsto (fun eta : ℝ=>sourceRegularMatrix 0*ᵥ((eta:ℂ) •
      (sourceFullCurrentResidue q n (eta:ℂ) l r-((eta:ℂ)⁻¹)^2 • sourceStaticCurrent q n l r)))
      (𝓝[>] 0) (𝓝 (sourceRegularMatrix 0*ᵥsourceCurrentSimple q n l r)) :=
    (continuous_const.matrix_mulVec continuous_id).continuousAt.tendsto.comp (sourceCurrent_simple_generated q n l r)
  have total := (tendsto_finsetSum Finset.univ (fun i _=>term i)).add regular
  simp only [zero_mul,zero_smul,add_zero] at total
  apply total.congr'
  filter_upwards [sourceStatic_causal_eventually n spatial,self_mem_nhdsWithin] with eta legal positive
  have nz : (eta:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,Function.comp_def]
  have channel (i : Fin 3) := laurent_channel (eta:ℂ)
    ((sourceChargedDenominator n (eta:ℂ) i)⁻¹) ((sourceChargedDenominator n 0 i)⁻¹)
    (sourceSlowRead (sourceActualNativeResidue q n (eta:ℂ) l r) ⟨i.val,by omega⟩)
    (sourceSlowRead (sourceStaticNative q n l r) ⟨i.val,by omega⟩) nz
    (sourceChargedChannel n 0 i) (sourceChargedChannel 0 1 i)
  simp only [←sourceChargedChannel_static_split] at channel
  simp_rw [←channel]
  rw [sourceChargedSecondField_channels q n ⟨(eta:ℂ),legal⟩,sourceChargedStaticDouble]
  simp only [smul_sub,smul_add,Finset.smul_sum,Finset.sum_sub_distrib,Matrix.mulVec_sub,Matrix.mulVec_smul]
  module

end LowEnergy.PreparationVacuumChargedLongRangeRead
