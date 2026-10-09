import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticCurrentResidue

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumObservedStaticResidue
open PreparationVacuumObservedPoleTensor PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalFeedback PreparationVacuumQuantumSlowResidue
open PreparationVacuumElectromagneticIdentity CanonicalGradedSpatialSource
open PreparationVacuumCausalPoleResponse PreparationVacuumPhysicalPoleSheet
open PreparationVacuumFullOriginResponse
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceGaugeCurrentResidue sourceFullCurrentResidue fullKernelFrame
  activeProjection fullInverse originalReadback

private theorem matrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms) := by
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

private theorem reader_continuous : Continuous sourceNativeReaderFirst := by
  unfold sourceNativeReaderFirst sourceLinearPart degreeTensor
  exact ((continuous_const.mul continuous_const).mul (matrix_continuous _)).sub
    (((((continuous_const.mul (matrix_continuous _)).mul continuous_const).mul continuous_const).mul continuous_const))

/-- The complete first spatial source-reader jet consumes all 289 resonant current entries. -/
def sourceStaticNative (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) : Fin 289→ℂ :=
  sourceNativeReaderFirst (fixedMomentum n 0)*ᵥsourceStaticCurrent q n l r

private theorem origin_smul (z w : ℂ) : z • sourceOriginPair w=sourceOriginPair (z*w) := by
  funext i
  simp only [sourceOriginPair,Pi.smul_apply,Pi.add_apply,Pi.single_apply]
  split_ifs <;> simp only [smul_eq_mul,mul_add,mul_zero]

private theorem origin_continuous : Continuous sourceOriginPair := by
  apply continuous_pi
  intro i
  simp only [sourceOriginPair,Pi.add_apply,Pi.single_apply]
  split_ifs <;> fun_prop

/-- The original gauge forcing retains its simple static coefficient. -/
theorem sourceStaticOrigin_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>(eta:ℂ) • sourceOriginCurrentResidue q n (eta:ℂ) l r)
      (𝓝[>] 0) (𝓝 (sourceOriginPair ((3/10:ℂ)*rootTwo*
        (sourceStaticGaugeCurrent q n l r 1 0-sourceStaticGaugeCurrent q n l r 2 1)))) := by
  have h:=(tendsto_const_nhds (x:=(3/10:ℂ)*rootTwo)).mul
    ((sourceStaticGaugeCurrent_generated q n l r 1 0).sub (sourceStaticGaugeCurrent_generated q n l r 2 1))
  have result:=origin_continuous.continuousAt.tendsto.comp h
  apply result.congr
  intro eta
  simp only [Function.comp_def,sourceOriginCurrentResidue,origin_smul]
  congr 1
  ring

/-- The actual native forcing has its static leading coefficient without discarding nongauge current. -/
theorem sourceStaticNative_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>((eta:ℂ)^2) • sourceActualNativeResidue q n (eta:ℂ) l r)
      (𝓝[>] 0) (𝓝 (sourceStaticNative q n l r)) := by
  have scalar : Tendsto (fun eta : ℝ=>(eta:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have origin:=scalar.smul (sourceStaticOrigin_generated q n l r)
  simp only [zero_smul,smul_smul,←pow_two] at origin
  have point : Continuous (fun eta : ℝ=>fixedMomentum n (eta:ℂ)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact Complex.continuous_ofReal
    · exact continuous_const
  have reader:=(reader_continuous.comp point).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have current:=sourceStaticCurrent_generated q n l r
  have product:=(continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp (reader.prodMk_nhds current)
  have result:=origin.add product
  simpa only [Function.comp_def,sourceActualNativeResidue,sourceStaticNative,zero_add,
    smul_add,Matrix.mulVec_smul,Complex.ofReal_zero] using result

/-- The original slow-coordinate reader consumes the complete generated static forcing. -/
theorem sourceStaticSlow_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>((eta:ℂ)^2) • sourceSlowRead (sourceActualNativeResidue q n (eta:ℂ) l r))
      (𝓝[>] 0) (𝓝 (sourceSlowRead (sourceStaticNative q n l r))) := by
  have continuous : Continuous sourceSlowRead := by
    apply continuous_pi
    intro i
    unfold sourceSlowRead
    split_ifs <;> fun_prop
  have h:=continuous.continuousAt.tendsto.comp (sourceStaticNative_generated q n l r)
  apply h.congr
  intro eta
  funext i
  simp only [Function.comp_def,sourceSlowRead,Matrix.mulVec_smul,Pi.smul_apply]
  split_ifs <;> simp only [smul_zero]

end LowEnergy.PreparationVacuumObservedStaticResidue
