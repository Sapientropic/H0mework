import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.Full
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.FullSpace.Source

/-! Physical-time dynamics of the source's charged occupied matter. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.Dynamics
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracCliffordRepresentation DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open Stage9DEF Stage9DEF.Compatibility YangMills.FullPairing
open LowEnergy.FullQuantum LowEnergy.FullQuantum.FullSpace
open StageNineCurrentCoframeMatterTemporalPrincipal SU7MotherLieAlgebra
open StageNineCoframeLocalDifferentiability StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open SU7MotherGaugeTheory SU7ExteriorBreakingYukawa
open StageNineDiracDualYukawaSpinJurisdiction StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open scoped Matrix
noncomputable section

theorem frequency_gauge : frequency = lapse * gaugeScale := by
  unfold frequency gaugeScale
  ring

theorem temporal_inverse (point : BasePoint) :
    currentCoframeMatterTemporalPrincipalInverse (actual.coframe point) =
      (lapse : ℂ) • (Complex.I • diracMatrixMatterAction diracGammaZero) := by
  rw [actual_coframe]
  have q : coframeTemporalPrincipalScalar (homogeneousCoframe lapse) = (lapse⁻¹)^2 := by
    rw [coframeTemporalPrincipalScalar, homogeneousCoframe_inv lapse lapse_pos.ne']
    simp [homogeneousCoframe, minkowskiInternalSign, Fin.sum_univ_four]
  apply LinearMap.ext
  intro v
  simp only [currentCoframeMatterTemporalPrincipalInverse, q,
    currentCoframeMatterTemporalPrincipal, LinearMap.smul_apply,
    homogeneousInverseGamma lapse lapse_pos.ne',
    diracMatrixMatterAction_smul_matrix, smul_smul]
  congr 1
  push_cast
  field_simp [lapse_pos.ne']

theorem gauge_original : gaugeMother =
    ((Complex.I * (lapse : ℂ)) * (gaugeScale : ℂ)) •
      ∑ j : Fin 3, (diracMatrixMatterAction (diracGammaZero * diracGamma j.succ)).comp
        (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator j))) := by
  apply LinearMap.ext
  intro v
  have spatial (j : Fin 3) :
      inverseCoframeDiracGamma {coframe := actual.coframe 0, derivative := 0} j.succ =
        diracGamma j.succ := by
    rw [actual_coframe, homogeneousInverseGamma lapse lapse_pos.ne']
    simp
  simp only [gaugeMother, YangMills.Response.Forcing.insertion,
    YangMills.Response.Forcing.spatialInsertion, sourceGaugeCoordinates_original,
    temporal_inverse, spatial, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    actual_connection_source]
  have timeZero : actual.gaugeConnection 0 0 = 0 := by simp [actual_gaugeConnection, gaugePotential]
  rw [timeZero]
  simp only [p286LieBlockEmbed_zero, diracExteriorMotherLieAction_zero_matrix,
    sub_zero, p286LieBlockEmbed_real_smul,
    diracExteriorMotherLieAction_real_smul, LinearMap.smul_apply,
    map_sum, map_smul, diracMatrixMatterAction_mul,
    LinearMap.comp_apply, Finset.smul_sum, smul_smul, smul_neg]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have coefficient : Complex.I * ((lapse : ℂ) * (Complex.I * (Complex.I * (gaugeScale : ℂ)))) =
      -(Complex.I * (lapse : ℂ) * (gaugeScale : ℂ)) := by
    calc
      _ = Complex.I^2 * (Complex.I * (lapse : ℂ) * (gaugeScale : ℂ)) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [coefficient]
  module

theorem spin_embed (matrix : DiracMatrix) (values : Source.Index → ℂ) :
    diracMatrixMatterAction matrix (embed values) =
      embed (fun i => ∑ spin, matrix i.1 spin * values (spin,i.2)) :=
  sourceColorDiracMatter_matrix matrix _

theorem generator_embed (axis : Fin 3) (values : Source.Index → ℂ) :
    diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator axis)) (embed values) =
      embed (fun i => ∑ color, values (i.1,color) * sourceColorPauli axis i.2 color) :=
  sourceColorDiracMatter_generator axis _

def gaugeValues (values : Source.Index → ℂ) (i : Source.Index) : ℂ :=
  (Complex.I * (lapse : ℂ) * (gaugeScale : ℂ)) *
    ∑ axis : Fin 3, ∑ spin, (diracGammaZero * diracGamma axis.succ) i.1 spin *
      ∑ color, values (spin,color) * sourceColorPauli axis i.2 color

theorem gauge_embed (values : Source.Index → ℂ) :
    gaugeMother (embed values) = embed (gaugeValues values) := by
  rw [gauge_original]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    generator_embed, spin_embed]
  rw [← map_sum, ← map_smul]
  rfl

def principalValues (momentum : Fin 3 → ℝ) (values : Source.Index → ℂ) (i : Source.Index) : ℂ :=
  ∑ axis : Fin 3, (-(lapse : ℂ) * (momentum axis : ℂ)) *
    ∑ spin, (diracGammaZero * diracGamma axis.succ) i.1 spin * values (spin,i.2)

theorem principal_embed (momentum : Fin 3 → ℝ) (values : Source.Index → ℂ) :
    principalMother momentum (embed values) = embed (principalValues momentum values) := by
  simp only [principalMother, LinearMap.sum_apply, LinearMap.smul_apply, spin_embed]
  simp only [← map_smul, ← map_sum]
  rfl

def spinValues (values : Source.Index → ℂ) (i : Source.Index) : ℂ :=
  (3*(lapse : ℂ)*(spinScale : ℂ)/2) * ∑ spin, diracGammaFive i.1 spin * values (spin,i.2)

theorem spinMother_embed (values : Source.Index → ℂ) :
    spinMother (embed values) = embed (spinValues values) := by
  simp only [spinMother, LinearMap.smul_apply, spin_embed, ← map_smul]
  rfl

/-- The entire occupied source is invariant before any coordinate readout. -/
theorem physical_free_embed (point : BasePoint) (momentum : Fin 3 → ℝ) (values : Source.Index → ℂ) :
    Triangular.freeHamiltonian actual point momentum (embed values) =
      embed (principalValues momentum values + spinValues values + gaugeValues values) := by
  rw [source_free_original]
  simp only [LinearMap.add_apply, principal_embed, spinMother_embed, gauge_embed, ← map_add]

def bandValues (first second : ℂ) : Source.Index → ℂ :=
  fun i => if i = (2,1) then first else if i = (3,0) then second else 0

/-- The original charged singlet and its momentum-coupled triplet form an invariant two-state channel. -/
theorem physical_free_band (point : BasePoint) (momentum : ℝ) (first second : ℂ) :
    Triangular.freeHamiltonian actual point ![0,0,momentum] (embed (bandValues first second)) =
      embed (bandValues
        (((2*frequency + lapse*momentum : ℝ) : ℂ)*first + (frequency : ℂ)*second)
        ((frequency : ℂ)*first + ((2*frequency-lapse*momentum : ℝ) : ℂ)*second)) := by
  rw [physical_free_embed]
  congr 1
  funext i
  rcases i with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    simp [principalValues, spinValues, gaugeValues, bandValues, sourceColorPauli,
      diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      diracGammaFive, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three,
      Fin.sum_univ_two, frequency, gaugeScale]
  all_goals ring_nf; simp [Complex.I_sq]
  all_goals ring

theorem yukawa_embed_zero (point : BasePoint) (values : Source.Index → ℂ) :
    diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar point))
      (embed values) = 0 := by
  rw [actual_scalar]
  simp only [sourceGeneratedVacuumCoordinates, scalarCoordinateEquiv.symm_apply_apply,
    diracDualRightChiralYukawaAction, LinearMap.comp_apply, spin_embed]
  funext spin
  change exteriorYukawaInternalAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
    (∑ color, (∑ other, rightChiralityProjector spin other * values (other,color)) •
      sourceColorDoubletMatter color) = 0
  simp only [map_sum, map_smul, sourceColorDoublet_internalYukawa_zero,
    smul_zero, Finset.sum_const_zero]

theorem physical_hamiltonian_embed (point : BasePoint) (momentum : Fin 3 → ℝ)
    (values : Source.Index → ℂ) :
    hamiltonian actual point momentum (embed values) =
      Triangular.freeHamiltonian actual point momentum (embed values) := by
  rw [Triangular.hamiltonian_split]
  simp only [LinearMap.add_apply, Triangular.interactionHamiltonian, Triangular.interaction,
    LinearMap.smul_apply, Module.End.mul_apply, yukawa_embed_zero, map_zero, smul_zero, add_zero]

theorem physical_band (point : BasePoint) (momentum : ℝ) (first second : ℂ) :
    hamiltonian actual point ![0,0,momentum] (embed (bandValues first second)) =
      embed (bandValues
        (((2*frequency + lapse*momentum : ℝ) : ℂ)*first + (frequency : ℂ)*second)
        ((frequency : ℂ)*first + ((2*frequency-lapse*momentum : ℝ) : ℂ)*second)) := by
  rw [physical_hamiltonian_embed, physical_free_band]

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.Dynamics
