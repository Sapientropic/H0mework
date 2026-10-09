import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceQuantumScalarOrbitDimensions
import H0mework.Versions.AE.Physics.LowEnergy.Electromagnetic.Action
import H0mework.Versions.AB.Physics.LowEnergy.Electromagnetic.ExternalState
import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Evolution
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalSourceColumns

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumElectromagneticIdentity
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage10 Stage10.CanonicalMatter
open YangMills.FullPairing Electromagnetic.ExternalState Stage9DEF Stage9DEF.Compatibility
open PreparationVacuumNativeSourceRestriction
open scoped BigOperators Matrix InnerProductSpace

/-- The original actual scalar fixes these directions, before any light-mode or charge-unit selection. -/
theorem sourceStabilizer_actual_scalar (direction : Fin 3) (point : BasePoint) :
    scalarMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction)) (actual.scalar point)=0 := by
  rw [actual_scalar]
  exact sourceColorP286Generator_vacuum_zero direction

def sourceChargeCoordinates (direction : Fin 3) (values : Source.Index→ℂ) (index : Source.Index) : ℂ :=
  Complex.I*∑ other : Fin 2,values (index.1,other)*sourceColorPauli direction index.2 other

def sourceChargeMatrix (direction : Fin 3) : Matrix Source.Index Source.Index ℂ :=
  fun row column=>if row.1=column.1 then Complex.I*sourceColorPauli direction row.2 column.2 else 0

theorem sourceCharge_coordinates (direction : Fin 3) (values : Source.Index→ℂ) (index : Source.Index) :
    coordinates (Electromagnetic.Action.canonicalDirection (sourceColorP286Generator direction) (embed values)) index=
      sourceChargeCoordinates direction values index := by
  rw [Electromagnetic.Action.canonical_coordinates]
  have hyper : (sourceColorP286Generator direction).2.2.1=(0 : ℂ) := by
    rw [sourceColorP286Generator_hypercharge_zero]
    rfl
  simp only [sourceColorP286Generator_topLeft,hyper,ite_self,add_zero]
  rfl

theorem sourceCharge_embedding (direction : Fin 3) (values : Source.Index→ℂ) :
    Electromagnetic.Action.canonicalDirection (sourceColorP286Generator direction) (embed values)=
      embed (sourceChargeCoordinates direction values) := by
  rw [Electromagnetic.Action.canonical_direction_source]
  change Complex.I • diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction))
      (sourceColorDiracMatter (fun spin color=>values (spin,color)))=
    sourceColorDiracMatter (fun spin color=>sourceChargeCoordinates direction values (spin,color))
  rw [sourceColorDiracMatter_generator,←sourceColorDiracMatter_smul]
  rfl

theorem sourceCharge_matrix_generated (direction : Fin 3) (values : Source.Index→ℂ) :
    sourceChargeMatrix direction *ᵥ values=sourceChargeCoordinates direction values := by
  funext index
  rcases index with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,sourceChargeMatrix,sourceChargeCoordinates,
      Fin.sum_univ_two]
  all_goals ring

theorem sourceCharge_hermitian (direction : Fin 3) : (sourceChargeMatrix direction).conjTranspose=sourceChargeMatrix direction := by
  ext row column
  rcases row with ⟨spin,color⟩
  rcases column with ⟨spin',color'⟩
  simp only [Matrix.conjTranspose_apply,sourceChargeMatrix]
  by_cases same : spin=spin'
  · subst spin'
    fin_cases direction <;> fin_cases color <;> fin_cases color' <;> norm_num [sourceColorPauli]
    all_goals ring
  · simp only [if_neg same,if_neg (Ne.symm same),star_zero]

theorem sourceCharge_square (direction : Fin 3) :
    sourceChargeMatrix direction*sourceChargeMatrix direction=(1/4 : ℂ) • (1 : Matrix Source.Index Source.Index ℂ) := by
  ext row column
  rcases row with ⟨spin,color⟩
  rcases column with ⟨spin',color'⟩
  fin_cases direction <;> fin_cases spin <;> fin_cases spin' <;> fin_cases color <;> fin_cases color' <;>
    norm_num [Matrix.mul_apply,Fintype.sum_prod_type,sourceChargeMatrix,sourceColorPauli,
      Fin.sum_univ_four,Fin.sum_univ_two,Matrix.smul_apply,Matrix.one_apply]
  all_goals apply Complex.ext <;> norm_num [Complex.mul_re,Complex.mul_im]

theorem sourceCharge_casimir :
    (∑ direction : Fin 3,sourceChargeMatrix direction*sourceChargeMatrix direction)=
      (3/4 : ℂ) • (1 : Matrix Source.Index Source.Index ℂ) := by
  simp only [sourceCharge_square,Fin.sum_univ_three,←add_smul]
  congr 1
  norm_num

def actualPoleCoordinates (point : BasePoint) (momentum : Fin 3→ℝ) : Source.Index→ℂ :=
  ChargedPreparation.CanonicalParticle.normalizedValues point momentum

def actualPolePreparation (momentum : Fin 3→ℝ) : Mother :=
  ChargedPreparation.CanonicalParticle.normalizedPreparation momentum

/-- The external state is generated on the original full Hamiltonian, rather than chosen by its charge weight. -/
theorem actualPole_hamiltonian (point : BasePoint) (momentum : Fin 3→ℝ) :
    FullQuantum.hamiltonian Runtime.configuration point momentum
      (actualPolePreparation momentum (actual.matter point))=
      (ChargedPreparation.CanonicalParticle.energy momentum : ℂ) •
        actualPolePreparation momentum (actual.matter point) := by
  have material : actual.matter point=(2 : ℂ) • embed (Source.vector point) := by
    apply naturalCoordinates.injective
    simpa only [map_smul,YangMills.FullPairing.prepared] using actual_eq_twice_prepared point
  rw [material,map_smul,map_smul]
  have eigen:=ChargedPreparation.CanonicalParticle.normalized_full_hamiltonian point momentum
  change FullQuantum.hamiltonian Runtime.configuration point momentum
    (actualPolePreparation momentum (embed (Source.vector point)))=_ at eigen
  rw [eigen]
  exact smul_comm _ _ _

def actualPoleChargeTransition (direction : Fin 3) (point : BasePoint) (left right : Fin 3→ℝ) : ℂ :=
  ∑ spin : Fin 4,∑ color : Fin 2,star (actualPoleCoordinates point left (spin,color))*
    sourceChargeCoordinates direction (actualPoleCoordinates point right) (spin,color)

theorem actualPole_current_transition (direction : Fin 3) (point : BasePoint) (left right : Fin 3→ℝ) :
    actual.conjugateMatter point
      (canonicalDual (actualPolePreparation left)
        (currentAction 0 (sourceColorP286Generator direction)
          (actualPolePreparation right (actual.matter point))))=
      4*(spinScale : ℂ)*actualPoleChargeTransition direction point left right := by
  rw [Electromagnetic.ExternalState.original_prepared_vertex]
  change 4*(spinScale : ℂ)*inner ℂ
      (operator (actualPolePreparation left) (YangMills.FullPairing.prepared point))
      (operator ((Electromagnetic.Action.canonicalDirection (sourceColorP286Generator direction)).comp (actualPolePreparation right))
        (YangMills.FullPairing.prepared point))=_
  have composed : operator ((Electromagnetic.Action.canonicalDirection (sourceColorP286Generator direction)).comp (actualPolePreparation right))
      (YangMills.FullPairing.prepared point)=
      operator (Electromagnetic.Action.canonicalDirection (sourceColorP286Generator direction))
        (operator (actualPolePreparation right) (YangMills.FullPairing.prepared point)) := by
    simp [YangMills.FullPairing.prepared,operator_coordinates]
  rw [composed]
  unfold actualPolePreparation
  rw [ChargedPreparation.CanonicalParticle.full_prepared,ChargedPreparation.CanonicalParticle.full_prepared,
    operator_coordinates,inner_embed]
  simp only [sourceCharge_coordinates,Fintype.sum_prod_type,actualPoleCoordinates,actualPoleChargeTransition]

/-- Charge mixing retains the complete actual source pole and both momenta. -/
theorem actualPole_current_matrix (direction : Fin 3) (point : BasePoint) (left right : Fin 3→ℝ) :
    actual.conjugateMatter point
      (canonicalDual (actualPolePreparation left)
        (currentAction 0 (sourceColorP286Generator direction)
          (actualPolePreparation right (actual.matter point))))=
      4*(spinScale : ℂ)*(∑ index : Source.Index,star (actualPoleCoordinates point left index)*
        (sourceChargeMatrix direction *ᵥ actualPoleCoordinates point right) index) := by
  rw [actualPole_current_transition,sourceCharge_matrix_generated]
  simp only [actualPoleChargeTransition,Fintype.sum_prod_type]


theorem sourceChargeCoordinates_smul (direction : Fin 3) (coefficient : ℂ) (values : Source.Index→ℂ) :
    sourceChargeCoordinates direction (coefficient • values)=coefficient • sourceChargeCoordinates direction values := by
  rw [←sourceCharge_matrix_generated,Matrix.mulVec_smul,sourceCharge_matrix_generated]

theorem sourceChargeCoordinates_square (direction : Fin 3) (values : Source.Index→ℂ) :
    sourceChargeCoordinates direction (sourceChargeCoordinates direction values)=(1/4 : ℂ) • values := by
  rw [←sourceCharge_matrix_generated direction values,←sourceCharge_matrix_generated,
    Matrix.mulVec_mulVec,sourceCharge_square,Matrix.smul_mulVec,Matrix.one_mulVec]

def actualPoleChargeSecondMoment (direction : Fin 3) (point : BasePoint) (momentum : Fin 3→ℝ) : ℂ :=
  ∑ index : Source.Index,star (actualPoleCoordinates point momentum index)*
    sourceChargeCoordinates direction (sourceChargeCoordinates direction (actualPoleCoordinates point momentum)) index

theorem actualPoleChargeSecondMoment_generated (direction : Fin 3) (point : BasePoint) (momentum : Fin 3→ℝ) :
    actualPoleChargeSecondMoment direction point momentum=1/4 := by
  unfold actualPoleChargeSecondMoment
  rw [sourceChargeCoordinates_square]
  simp only [Pi.smul_apply,smul_eq_mul]
  have ordered : (∑ index : Source.Index,star (actualPoleCoordinates point momentum index)*
      ((1/4 : ℂ)*actualPoleCoordinates point momentum index))=
      (1/4 : ℂ)*∑ index : Source.Index,star (actualPoleCoordinates point momentum index)*actualPoleCoordinates point momentum index := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [ordered]
  change (1/4 : ℂ)*(∑ index : Source.Index,star (ChargedPreparation.CanonicalParticle.normalizedValues point momentum index)*
    ChargedPreparation.CanonicalParticle.normalizedValues point momentum index)=1/4
  rw [ChargedPreparation.CanonicalParticle.normalized_values_square,mul_one]

private def poleCoefficientCoordinates (momentum : Fin 3→ℝ) : Source.Index→ℂ :=
  ChargedPreparation.CanonicalParticle.upperValues (ChargedPreparation.CanonicalParticle.coefficients momentum)

private theorem poleCoefficientCharge_generated (direction : Fin 3) (momentum : Fin 3→ℝ) :
    (∑ spin : Fin 4,∑ color : Fin 2,star (poleCoefficientCoordinates momentum (spin,color))*
      sourceChargeCoordinates direction (poleCoefficientCoordinates momentum) (spin,color))=
      -2*(lapse : ℂ)*((ChargedPreparation.SpatialSpectrum.rate momentum+frequency : ℝ) : ℂ)*(momentum direction : ℂ) := by
  fin_cases direction <;>
    simp [poleCoefficientCoordinates,sourceChargeCoordinates,ChargedPreparation.CanonicalParticle.upperValues,
      ChargedPreparation.CanonicalParticle.coefficients,sourceColorPauli,Fin.sum_univ_four,Fin.sum_univ_two]
  all_goals ring_nf; simp only [Complex.I_sq]; ring

private theorem actualPole_coordinates_factor (point : BasePoint) (momentum : Fin 3→ℝ) :
    actualPoleCoordinates point momentum=
      ((ChargedPreparation.CanonicalParticle.normalization momentum : ℂ)*ChargedPreparation.CanonicalParticle.amplitude point) •
        poleCoefficientCoordinates momentum := by
  unfold actualPoleCoordinates ChargedPreparation.CanonicalParticle.normalizedValues ChargedPreparation.CanonicalParticle.values
    poleCoefficientCoordinates
  rw [ChargedPreparation.CanonicalParticle.upperValues_smul,smul_smul]

/-- The actual pole's form factor retains its momentum and the original source time and coframe parameters. -/
theorem actualPoleCharge_formFactor (direction : Fin 3) (point : BasePoint) (momentum : Fin 3→ℝ) :
    actualPoleChargeTransition direction point momentum momentum=
      -(lapse : ℂ)*(momentum direction : ℂ)/(2*(ChargedPreparation.SpatialSpectrum.rate momentum : ℂ)) := by
  have factor : actualPoleChargeTransition direction point momentum momentum=
      (ChargedPreparation.CanonicalParticle.normalization momentum : ℂ)^2*
      (star (ChargedPreparation.CanonicalParticle.amplitude point)*ChargedPreparation.CanonicalParticle.amplitude point)*
      (∑ spin : Fin 4,∑ color : Fin 2,star (poleCoefficientCoordinates momentum (spin,color))*
        sourceChargeCoordinates direction (poleCoefficientCoordinates momentum) (spin,color)) := by
    unfold actualPoleChargeTransition
    rw [actualPole_coordinates_factor,sourceChargeCoordinates_smul]
    simp only [Pi.smul_apply,smul_eq_mul,star_mul,Complex.star_def,Complex.conj_ofReal]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro spin _
    apply Finset.sum_congr rfl
    intro color _
    ring
  rw [factor,ChargedPreparation.CanonicalParticle.amplitude_square,poleCoefficientCharge_generated]
  have normalization:=ChargedPreparation.CanonicalParticle.normalized_weight_complex momentum
  have ratePositive : 0<ChargedPreparation.SpatialSpectrum.rate momentum := by
    apply Real.sqrt_pos.mpr
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos ChargedPreparation.Dispersion.frequency_pos)
      (mul_nonneg (sq_nonneg lapse) (ChargedPreparation.SpatialSpectrum.spatialSquare_nonneg momentum))
  have rateNonzero : (ChargedPreparation.SpatialSpectrum.rate momentum : ℂ)≠0 := Complex.ofReal_ne_zero.mpr ratePositive.ne'
  field_simp [rateNonzero]
  push_cast at normalization ⊢
  simp only [ChargedPreparation.CanonicalParticle.weight,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_ofNat] at normalization
  linear_combination (-(lapse : ℂ)*(momentum direction : ℂ))*normalization


/-- The same action-normalized external pole generates its full stabilizer-current tensor. -/
theorem actualPole_current_formFactor (direction : Fin 3) (point : BasePoint) (momentum : Fin 3→ℝ) :
    actual.conjugateMatter point
      (canonicalDual (actualPolePreparation momentum)
        (currentAction 0 (sourceColorP286Generator direction)
          (actualPolePreparation momentum (actual.matter point))))=
      -(Stage10.ActionNormalization.phaseMomentum : ℂ)*(lapse : ℂ)*(momentum direction : ℂ)/
        (2*(ChargedPreparation.SpatialSpectrum.rate momentum : ℂ)) := by
  rw [actualPole_current_transition,actualPoleCharge_formFactor,Stage10.ActionNormalization.phaseMomentum_source]
  push_cast
  ring

end LowEnergy.PreparationVacuumElectromagneticIdentity
