import H0mework.Physics.LowEnergy.LightInteraction.Native

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightInteraction
open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineConnectionSectorSourceBalance StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity Stage9C.Material.SpinPair
open SU7MotherLieAlgebra SU7MotherGaugeTheory StageNineEnrichedProofFreeSource
open MatterSpace StageNineDynamicBreakingVacuum
open scoped Kronecker Matrix
noncomputable section

def lightCoframe (c : Fin 5 → ℝ) : LorentzianCoframe :=
  !![c 0,0,0,0;0,c 1,0,0;0,0,c 2,0;c 4,0,0,c 3]

def sourceGenerator : P286LieBlockData := (2 : ℝ) • sourceColorP286Generator 0

def sourceGaugeData : LorentzianIndex → P286LieBlockData := Pi.single 1 sourceGenerator

def sourceGaugeOneForm : P286GaugeOneForm := fun mu => p286CoordinateEquiv (sourceGaugeData mu)

theorem source_generator_scalar_zero (mu : LorentzianIndex) :
    scalarMotherLieAction (p286LieBlockEmbed (sourceGaugeData mu))
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)=0 := by
  by_cases chosen : mu=1
  · subst mu
    simp only [sourceGaugeData,Pi.single_eq_same,sourceGenerator,p286LieBlockEmbed_real_smul,
      scalarMotherLieAction_real_smul,sourceColorP286Generator_vacuum_zero,smul_zero]
  · simp [sourceGaugeData,chosen,p286LieBlockEmbed_zero,scalarMotherLieAction_zero_matrix]

theorem source_scalar_variation_zero (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (scalar : C.scalar point=sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) :
    holonomicScalarGaugeConnectionVariation C (fun _ => sourceGaugeOneForm) point=0 := by
  funext mu
  change scalarMotherLieAction
    (p286LieBlockEmbed (p286CoordinateEquiv.symm (sourceGaugeOneForm mu))) (C.scalar point)=0
  rw [sourceGaugeOneForm,p286CoordinateEquiv.symm_apply_apply,scalar,source_generator_scalar_zero]

theorem source_curvature_quadratic_zero (point : BasePoint) :
    p286GaugeConnectionQuadraticCurvatureVariation (fun _ => sourceGaugeOneForm) point=0 := by
  funext pair
  fin_cases pair <;> simp [p286GaugeConnectionQuadraticCurvatureVariation,sourceGaugeOneForm,
    sourceGaugeData,pairFirst,pairSecond]

theorem light_coframe_adjugate (c : Fin 5 → ℝ) (a : LorentzianIndex) :
    (lightCoframe c).adjugate 1 a=if a=1 then c 0*c 2*c 3 else 0 := by
  let minors : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ :=
    ![!![0,0,0;0,c 2,0;c 4,0,c 3],!![c 0,0,0;0,c 2,0;c 4,0,c 3],
      !![c 0,0,0;0,0,0;c 4,0,c 3],!![c 0,0,0;0,0,0;0,c 2,0]]
  have read (j : Fin 4) : (lightCoframe c).submatrix j.succAbove (1 : Fin 4).succAbove=minors j := by
    ext i k
    fin_cases j <;> fin_cases i <;> fin_cases k <;> rfl
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix,read,Matrix.det_fin_three]
  fin_cases a <;> simp [minors]

def sourcePair (psi : DiracExteriorMatterCarrier) (chi : Module.Dual ℂ DiracExteriorMatterCarrier) : ℝ :=
  (chi (Complex.I • diracMatrixMatterAction (diracGamma 1)
    (diracExteriorMotherLieAction (p286LieBlockEmbed sourceGenerator) psi))).re

theorem selected_current_polynomial (c : Fin 5 → ℝ)
    (psi : DiracExteriorMatterCarrier) (chi : Module.Dual ℂ DiracExteriorMatterCarrier) :
    adjugateCurrent (lightCoframe c) sourceGaugeData psi chi=c 0*c 2*c 3*sourcePair psi chi := by
  unfold adjugateCurrent
  rw [Finset.sum_eq_single (1 : LorentzianIndex)]
  · simp only [sourceGaugeData,Pi.single_eq_same,light_coframe_adjugate]
    simp [sourcePair]
  · intro mu _ different
    simp [sourceGaugeData,different,p286LieBlockEmbed_zero,
      diracExteriorMotherLieAction_zero_matrix]
  · simp

def sourceVertex : Matrix SourceIndex SourceIndex ℂ :=
  Complex.I • (diracGamma 1 ⊗ₖ tripletGaugeMatrix sourceGenerator)

theorem source_pair_triplet (psi : SourceIndex → ℂ) (chi : Module.Dual ℂ DiracExteriorMatterCarrier) :
    sourcePair (tripletLift psi) chi=
      (∑ i, tripletDualRead chi i*(sourceVertex *ᵥ psi) i).re := by
  have generated := tripletLift_spin_gauge (diracGamma 1) sourceGenerator psi
  unfold sourcePair sourceVertex
  rw [← generated,← map_smul,tripletDualRead_apply]
  simp only [Matrix.smul_mulVec]

theorem selected_original_current (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (c : Fin 5 → ℝ) (same : C.coframe point=lightCoframe c) (positive : 0<(lightCoframe c).det) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource C sourceGaugeOneForm point=
      c 0*c 2*c 3*sourcePair (C.matter point) (C.conjugateMatter point) := by
  rw [original_current_adjugate C sourceGaugeOneForm point (same.symm ▸ positive),same]
  have data : (fun mu => p286CoordinateEquiv.symm (sourceGaugeOneForm mu))=sourceGaugeData := by
    funext mu
    exact p286CoordinateEquiv.symm_apply_apply _
  rw [data,selected_current_polynomial]

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightInteraction
