import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceQuantumBoundaryNumerator

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumObservedBoundaryResidue
open CanonicalGradedSpatialSource PreparationVacuumObservedPoleTensor
open PreparationVacuumNativeSlowCoupling PreparationVacuumQuantumSlowResidue
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback
open PreparationVacuumFullOriginResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumCausalPoleResponse
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceNativeReaderFirst sourceActualNativeResidue
  sourceWholeCurrentNumerator sourceGaugeCurrentNumerator

def sourceOriginGaugeNumerator (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  sourceOriginPair ((3/10:ℂ)*rootTwo*(sourceGaugeCurrentNumerator q n c eta l r 1 0-
    sourceGaugeCurrentNumerator q n c eta l r 2 1))

/-- The native derivative multiplies the complete second-order quantum current. -/
def sourceNativeBoundaryNumerator (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  (eta:ℂ) • sourceOriginGaugeNumerator q n c eta l r+
    sourceNativeReaderFirst (fixedMomentum n (sourcePoleSide c eta))*ᵥsourceWholeCurrentNumerator q n c eta l r

private theorem origin_pair_smul (z w : ℂ) : sourceOriginPair (z*w)=z • sourceOriginPair w := by
  funext i
  simp only [sourceOriginPair,Pi.add_apply,Pi.single_apply,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring

theorem sourceOriginGaugeNumerator_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (c eta : ℝ) (positive : 0<eta) (l r : RestStateIndex) :
    (eta:ℂ) • sourceOriginCurrentResidue q n (sourcePoleSide c eta) l r=
      sourceOriginGaugeNumerator q n c eta l r := by
  unfold sourceOriginGaugeNumerator sourceOriginCurrentResidue
  rw [←sourceGaugeCurrentNumerator_generated q n c eta positive l r 1 0,
    ←sourceGaugeCurrentNumerator_generated q n c eta positive l r 2 1]
  rw [←origin_pair_smul]
  congr 1
  ring

theorem sourceNativeBoundaryNumerator_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (c eta : ℝ) (positive : 0<eta) (l r : RestStateIndex) :
    ((eta:ℂ)^2) • sourceActualNativeResidue q n (sourcePoleSide c eta) l r=
      sourceNativeBoundaryNumerator q n c eta l r := by
  rw [sourceActualNativeResidue,smul_add,sourceNativeBoundaryNumerator,
    ←sourceOriginGaugeNumerator_generated q n c eta positive l r,
    ←sourceWholeCurrentNumerator_generated q n c eta positive l r]
  rw [smul_smul,←pow_two,Matrix.mulVec_smul]

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

theorem sourceNativeFirst_continuous : Continuous sourceNativeReaderFirst := by
  have first : Continuous (sourceLinearPart sourceReadbackTerms) :=
    source_matrix_continuous _
  have second : Continuous (sourceLinearPart activeTerms) :=
    source_matrix_continuous _
  unfold sourceNativeReaderFirst
  exact (continuous_const.matrix_mul first).sub
    (((continuous_const.matrix_mul second).matrix_mul continuous_const).matrix_mul continuous_const |>.matrix_mul continuous_const)

private theorem origin_pair_continuous : Continuous sourceOriginPair := by
  apply continuous_pi
  intro i
  simp only [sourceOriginPair,Pi.add_apply,Pi.single_apply]
  split_ifs <;> fun_prop

theorem sourceOriginGaugeNumerator_limit (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ)
    (l r : RestStateIndex) :
    Tendsto (fun eta=>sourceOriginGaugeNumerator q n c eta l r) (𝓝 0)
      (𝓝 (sourceOriginGaugeNumerator q n c 0 l r)) := by
  have difference:=(sourceGaugeCurrentNumerator_limit q n c l r 1 0).sub
    (sourceGaugeCurrentNumerator_limit q n c l r 2 1)
  have weight:=(tendsto_const_nhds (x:=(3/10:ℂ)*rootTwo)).mul difference
  exact origin_pair_continuous.continuousAt.tendsto.comp weight

/-- The complete source coefficient at the quantum boundary retains every nongauge entry. -/
def sourceNativeBoundaryResidue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  sourceNativeReaderFirst (fixedMomentum n (Complex.I*(c:ℂ)))*ᵥsourceWholeCurrentNumerator q n c 0 l r

theorem sourceNativeBoundaryNumerator_limit (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ)
    (l r : RestStateIndex) :
    Tendsto (fun eta=>sourceNativeBoundaryNumerator q n c eta l r) (𝓝 0)
      (𝓝 (sourceNativeBoundaryResidue q n c l r)) := by
  have origin:=(Complex.continuous_ofReal.tendsto (0:ℝ)).smul (sourceOriginGaugeNumerator_limit q n c l r)
  have momentum : Tendsto (fun eta=>fixedMomentum n (sourcePoleSide c eta)) (𝓝 0)
      (𝓝 (fixedMomentum n (Complex.I*(c:ℂ)))) := by
    have continuous : Continuous (fun eta=>fixedMomentum n (sourcePoleSide c eta)) := by
      unfold fixedMomentum sourcePoleSide fullMomentum
      apply continuous_pi
      intro i
      fin_cases i
      · change Continuous (fun eta : ℝ=>(eta:ℂ)+Complex.I*(c:ℂ))
        fun_prop
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
    simpa only [sourcePoleSide,Complex.ofReal_zero,zero_add] using continuous.tendsto 0
  have reader:=sourceNativeFirst_continuous.continuousAt.tendsto.comp momentum
  have product:=(continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    (reader.prodMk_nhds (sourceWholeCurrentNumerator_limit q n c l r))
  have limit:=origin.add product
  simpa only [Function.comp_def,Complex.ofReal_zero,zero_smul,zero_add,
    sourceNativeBoundaryNumerator,sourceNativeBoundaryResidue] using limit

theorem sourceActualNative_boundary_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c : ℝ)
    (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>((eta:ℂ)^2) • sourceActualNativeResidue q n (sourcePoleSide c eta) l r)
      (𝓝[>] 0) (𝓝 (sourceNativeBoundaryResidue q n c l r)) := by
  apply ((sourceNativeBoundaryNumerator_limit q n c l r).mono_left nhdsWithin_le_nhds).congr'
  have positive : ∀ᶠ eta : ℝ in 𝓝[>] 0,0<eta := self_mem_nhdsWithin
  filter_upwards [positive] with eta pos
  exact (sourceNativeBoundaryNumerator_generated q n c eta pos l r).symm

end LowEnergy.PreparationVacuumObservedBoundaryResidue
