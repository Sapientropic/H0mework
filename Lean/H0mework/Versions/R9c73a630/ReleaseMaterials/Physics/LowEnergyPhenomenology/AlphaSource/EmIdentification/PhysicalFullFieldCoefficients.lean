import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationMixedDensityContacts
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldTangentCurrent
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.Electromagnetic.CanonicalCoframe

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalFullFieldScattering
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldCovector
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField SU7MotherLieAlgebra StageNineLorentzConnectionVariation
open PointwiseDiracSpinConnectionLift DiracCliffordRepresentation DiracExteriorMatterAction
open SU7ExteriorBreakingYukawa StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum SourceQuantumScalarChart SourceQuantumNativeDimensions
open StageNineCoframeScalarMatterRegularity StageNineP286GaugeConnectionVariation
open SU7MotherGaugeTheory
open FullQuantum.StateGreen FullQuantum.Triangular YangMills.FullPairing
open FullQuantum.CoframeResponse FullQuantum.FullSpace
open Electromagnetic.CanonicalCoframe
open scoped Matrix BigOperators Topology InnerProductSpace

local instance coeffIndexDecidable : DecidableEq Quantum.Index := Classical.decEq _

/-- The Lorentz bivector-one-form slot is a coordinate projection of the
    289 real field, real-linear entrywise. -/
def fieldLorentzLinear : Field289 →ₗ[ℝ] LorentzBivectorOneForm where
  toFun := fieldLorentz
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The gauge slot is the finite source sum of `originalUnit` directions,
    kept real-linear into the P286 Lie-block data. -/
def fieldGaugeDataLinear (mu : Fin 4) : Field289 →ₗ[ℝ] P286LieBlockData :=
  p286CoordinateEquiv.symm.toLinearMap.comp
    ({ toFun := fun f => fieldGauge f mu
       map_add' := fun f g => by
         unfold fieldGauge
         simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
       map_smul' := fun r f => by
         unfold fieldGauge
         simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply,
           smul_smul, smul_eq_mul] } :
      Field289 →ₗ[ℝ] NativeLie)

/-- The scalar slot is the finite source sum over the original J columns. -/
def fieldScalarLinear : Field289 →ₗ[ℝ] ScalarCoordinateCarrier where
  toFun := fieldScalar
  map_add' := fun f g => by
    unfold fieldScalar
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := fun r f => by
    unfold fieldScalar
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply,
      smul_smul, smul_eq_mul]

/-- The raised Lorentz connection is linear in the bivector one-form: each
    entry is a fixed sign times a linear combination of its coordinates. -/
private def lorentzSkewLinear :
    LorentzBivectorOneForm →ₗ[ℝ] PointwiseLorentzSpinConnection where
  toFun := lorentzSkewConnectionOfBivectorOneForm
  map_add' := fun a b => by
    funext fd io ii
    simp only [lorentzSkewConnectionOfBivectorOneForm, Pi.add_apply,
      loweredLorentzBivectorMatrix]
    have expand :
        (∑ x : Fin 6,
            (a fd x + b fd x) * orientedLorentzBivectorBasisCoefficient x io ii) =
          (∑ x : Fin 6, a fd x * orientedLorentzBivectorBasisCoefficient x io ii) +
            ∑ x : Fin 6, b fd x * orientedLorentzBivectorBasisCoefficient x io ii := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro pair _
      rw [add_mul]
    rw [expand, mul_add]
  map_smul' := fun r a => by
    funext fd io ii
    simp only [lorentzSkewConnectionOfBivectorOneForm, Pi.smul_apply,
      loweredLorentzBivectorMatrix, RingHom.id_apply, smul_eq_mul]
    rw [show (∑ x : Fin 6,
            r * a fd x * orientedLorentzBivectorBasisCoefficient x io ii) =
          r * ∑ x : Fin 6, a fd x * orientedLorentzBivectorBasisCoefficient x io ii
      from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro pair _
        ring]
    ring

/-- The spin-connection leg of the source connection, real-linear in the
    Lorentz slot through the generated Dirac lift packaging. -/
def lorentzConnectionLinear (mu : Fin 4) :
    LorentzBivectorOneForm →ₗ[ℝ] DiracMatrix :=
  (diracSpinConnectionLiftLinear mu).comp lorentzSkewLinear

/-- The P286 Lie-block embed is real-linear into the mother Lie carrier:
    the subtype equality reduces to the raw block matrix.  The public source
    facts are `SU7MotherGaugeTheory.p286LieBlockEmbed_add` and
    `StageNineP286GaugeConnectionVariation.p286LieBlockEmbed_real_smul`. -/
def p286EmbedLinear : P286LieBlockData →ₗ[ℝ] SU7MotherLieMatrix where
  toFun := p286LieBlockEmbed
  map_add' := SU7MotherGaugeTheory.p286LieBlockEmbed_add
  map_smul' := fun r a => by
    rw [StageNineP286GaugeConnectionVariation.p286LieBlockEmbed_real_smul]
    rfl

/-- The Dirac mother Lie action is real-linear in the matrix, from the public
    generated facts. -/
def diracMotherLieLinear :
    SU7MotherLieMatrix →ₗ[ℝ] Module.End ℂ DiracExteriorMatterCarrier where
  toFun := diracExteriorMotherLieAction
  map_add' := StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_add
  map_smul' := fun r m => by
    rw [StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_real_smul,
      RingHom.id_apply]
    rfl

/-- The Dirac matrix-matter action is linear in its matrix argument
    entrywise. -/
def diracMatterActionLinear :
    DiracMatrix →ₗ[ℝ] Module.End ℂ DiracExteriorMatterCarrier where
  toFun := diracMatrixMatterAction
  map_add' := fun a b => LinearMap.ext fun field =>
    StageNineP286GaugeConnectionVariationDensity.diracMatrixMatterAction_add_matrix
      a b field
  map_smul' := fun r m => LinearMap.ext fun field => by
    simp only [LinearMap.smul_apply, RingHom.id_apply]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r m,
      StageNineP286GaugeConnectionVariationDensity.diracMatrixMatterAction_smul_matrix]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) r
      (diracMatrixMatterAction m field)).symm

/-- The right-chiral Yukawa sandwich is real-linear in the breaking scalar:
    the interior action is ℂ-linear and the outer leg is fixed. -/
def diracYukawaLinear :
    ExteriorBreakingScalarCarrier →ₗ[ℝ] Module.End ℂ DiracExteriorMatterCarrier where
  toFun := diracDualRightChiralYukawaAction
  map_add' := fun a b => by
    unfold diracDualRightChiralYukawaAction
    rw [StageNineCoframeScalarMatterRegularity.diracExteriorYukawaInternalAction_add,
      LinearMap.add_comp]
  map_smul' := fun r s => by
    unfold diracDualRightChiralYukawaAction
    rw [RingHom.id_apply]
    rw [show (r • s : ExteriorBreakingScalarCarrier) = ((r:ℂ) • s) from rfl]
    rw [StageNineCoframeScalarMatterRegularity.diracExteriorYukawaInternalAction_smul]
    rw [LinearMap.smul_comp]
    rfl

/-- The operator-matrix read is ℂ-linear, restricted here to the real
    scalars of the source construction. -/
def opMatReal :
    Module.End ℂ DiracExteriorMatterCarrier →ₗ[ℝ] SourceMatrix :=
  Quantum.operatorMatrix.toLinearEquiv.toLinearMap.restrictScalars ℝ

/-- The gauge leg of the source connection through the mother embed. -/
private def gaugeConnectionLinear (mu : Fin 4) :
    Field289 →ₗ[ℝ] Module.End ℂ DiracExteriorMatterCarrier :=
  (diracMotherLieLinear.comp p286EmbedLinear).comp (fieldGaugeDataLinear mu)

/-- The Lorentz leg through the spin lift and Dirac matrix-matter action. -/
private def spinConnectionLinear (mu : Fin 4) :
    Field289 →ₗ[ℝ] Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatterActionLinear.comp ((lorentzConnectionLinear mu).comp fieldLorentzLinear)

/-- The source connection direction as a real-linear map of the 289 field. -/
def sourceConnectionLinear (mu : Fin 4) : Field289 →ₗ[ℝ] SourceMatrix :=
  opMatReal.comp ((spinConnectionLinear mu) + (gaugeConnectionLinear mu))

/-- The source scalar direction as a real-linear map of the 289 field. -/
def sourceScalarLinear : Field289 →ₗ[ℝ] SourceMatrix :=
  opMatReal.comp
    (diracYukawaLinear.comp
      (LinearMap.comp
        (scalarCoordinateEquiv.symm.toLinearMap.restrictScalars ℝ)
        fieldScalarLinear))

/-- `sourceConnectionLinear` unfolds to the actual source connection. -/
theorem sourceConnectionLinear_eq (f : Field289) (mu : Fin 4) :
    sourceConnectionLinear mu f = connectionDirection (sourceField f) mu := by
  unfold sourceConnectionLinear opMatReal spinConnectionLinear gaugeConnectionLinear
    lorentzConnectionLinear lorentzSkewLinear diracMatterActionLinear
    fieldGaugeDataLinear fieldLorentzLinear connectionDirection sourceField
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.coe_mk,
    LinearEquiv.coe_toLinearMap, LinearMap.coe_restrictScalars]
  rfl

/-- `sourceScalarLinear` unfolds to the actual source scalar direction. -/
theorem sourceScalarLinear_eq (f : Field289) :
    sourceScalarLinear f = scalarDirection (sourceField f) := by
  unfold sourceScalarLinear opMatReal diracYukawaLinear fieldScalarLinear
    scalarDirection sourceField
  simp only [LinearMap.comp_apply, LinearMap.coe_mk, LinearEquiv.coe_toLinearMap,
    LinearMap.coe_restrictScalars]
  rfl

/-- The coframe projection of the assembled source field is additive. -/
theorem sourceField_coframe_add (f g : Field289) :
    (sourceField (f+g)).coframe = (sourceField f).coframe+(sourceField g).coframe :=
  fieldCoframeLinear.map_add f g

theorem sourceField_coframe_smul (r : ℝ) (f : Field289) :
    (sourceField (r • f)).coframe = r • (sourceField f).coframe :=
  fieldCoframeLinear.map_smul r f

theorem sourceField_conn_add (f g : Field289) (mu : Fin 4) :
    connectionDirection (sourceField (f+g)) mu =
      connectionDirection (sourceField f) mu+connectionDirection (sourceField g) mu := by
  rw [← sourceConnectionLinear_eq (f+g) mu, ← sourceConnectionLinear_eq f mu,
    ← sourceConnectionLinear_eq g mu]
  exact (sourceConnectionLinear mu).map_add f g

theorem sourceField_conn_smul (r : ℝ) (f : Field289) (mu : Fin 4) :
    connectionDirection (sourceField (r • f)) mu =
      r • connectionDirection (sourceField f) mu := by
  rw [← sourceConnectionLinear_eq (r • f) mu, ← sourceConnectionLinear_eq f mu]
  exact (sourceConnectionLinear mu).map_smul r f

theorem sourceField_scalar_add (f g : Field289) :
    scalarDirection (sourceField (f+g)) =
      scalarDirection (sourceField f)+scalarDirection (sourceField g) := by
  rw [← sourceScalarLinear_eq (f+g), ← sourceScalarLinear_eq f,
    ← sourceScalarLinear_eq g]
  exact sourceScalarLinear.map_add f g

theorem sourceField_scalar_smul (r : ℝ) (f : Field289) :
    scalarDirection (sourceField (r • f)) = r • scalarDirection (sourceField f) := by
  rw [← sourceScalarLinear_eq (r • f), ← sourceScalarLinear_eq f]
  exact sourceScalarLinear.map_smul r f

/-- The densitized lower direction is additive in its coframe direction:
    both factors are `fderiv` evaluations. -/
private theorem densitizedLower_add (a b : LorentzianCoframe) :
    densitizedLowerDirection 0 0 (a+b) =
      densitizedLowerDirection 0 0 a+densitizedLowerDirection 0 0 b := by
  unfold densitizedLowerDirection lowerDirection volumeDirection
  simp only [map_add, Complex.ofReal_add, add_smul, smul_add]
  module

private theorem densitizedLower_smul (r : ℝ) (a : LorentzianCoframe) :
    densitizedLowerDirection 0 0 (r • a) = r • densitizedLowerDirection 0 0 a := by
  unfold densitizedLowerDirection lowerDirection volumeDirection
  simp only [map_smul]
  rw [smul_eq_mul, Complex.ofReal_mul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  module

private theorem densitizedPrincipal_add (a b : LorentzianCoframe) :
    densitizedPrincipalDirection 0 (a+b) =
      densitizedPrincipalDirection 0 a+densitizedPrincipalDirection 0 b := by
  unfold densitizedPrincipalDirection principalDirection volumeDirection
  simp only [map_add, Complex.ofReal_add, add_smul, smul_add]
  module

private theorem densitizedPrincipal_smul (r : ℝ) (a : LorentzianCoframe) :
    densitizedPrincipalDirection 0 (r • a) = r • densitizedPrincipalDirection 0 a := by
  unfold densitizedPrincipalDirection principalDirection volumeDirection
  simp only [map_smul]
  rw [smul_eq_mul, Complex.ofReal_mul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  module

private theorem densitySpatialJet_add (a b : LorentzianCoframe) (j : Fin 3) :
    densitySpatialJet (a+b) j = densitySpatialJet a j+densitySpatialJet b j := by
  unfold densitySpatialJet coefficientJet volumeDirection
  simp only [map_add, Complex.ofReal_add, add_smul, smul_add]
  module

private theorem densitySpatialJet_smul (r : ℝ) (a : LorentzianCoframe) (j : Fin 3) :
    densitySpatialJet (r • a) j = r • densitySpatialJet a j := by
  unfold densitySpatialJet coefficientJet volumeDirection
  simp only [map_smul]
  rw [smul_eq_mul, Complex.ofReal_mul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  module

/-- The full coframe density row is additive in the coframe direction. -/
private theorem coframeDensityCoefficients_add (a b : LorentzianCoframe) (i : Fin 4) :
    coframeDensityCoefficients (a+b) i =
      coframeDensityCoefficients a i+coframeDensityCoefficients b i := by
  induction i using Fin.cases with
  | zero =>
      simp only [coframeDensityCoefficients, Fin.cases_zero]
      rw [densitizedLower_add, densitizedPrincipal_add, add_mul, smul_add]
      module
  | succ j =>
      simp only [coframeDensityCoefficients, Fin.cases_succ]
      rw [densitySpatialJet_add, densitizedPrincipal_add, add_mul, smul_add]
      module

private theorem coframeDensityCoefficients_smul (r : ℝ) (a : LorentzianCoframe)
    (i : Fin 4) :
    coframeDensityCoefficients (r • a) i =
      r • coframeDensityCoefficients a i := by
  induction i using Fin.cases with
  | zero =>
      simp only [coframeDensityCoefficients, Fin.cases_zero]
      rw [densitizedLower_smul, densitizedPrincipal_smul]
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_mul_assoc]
      module
  | succ j =>
      simp only [coframeDensityCoefficients, Fin.cases_succ]
      rw [densitySpatialJet_smul, densitizedPrincipal_smul]
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_mul_assoc]
      module

/-- The original density coefficients are additive in the 289-field. -/
theorem fieldDensityCoefficients_add (f g : Field289) (i : Fin 4) :
    fieldDensityCoefficients (sourceField (f+g)) i =
      fieldDensityCoefficients (sourceField f) i+
        fieldDensityCoefficients (sourceField g) i := by
  unfold fieldDensityCoefficients
  rw [sourceField_coframe_add, coframeDensityCoefficients_add]
  split_ifs with h
  · have sumSplit : (∑ mu : Fin 4,
          FullQuantum.CoframeResponse.coefficientMatrix mu
            (Stage9C.Material.SpinPair.actual.coframe 0) *
            connectionDirection (sourceField (f+g)) mu) =
        (∑ mu : Fin 4,
          FullQuantum.CoframeResponse.coefficientMatrix mu
            (Stage9C.Material.SpinPair.actual.coframe 0) *
            connectionDirection (sourceField f) mu) +
          ∑ mu : Fin 4,
            FullQuantum.CoframeResponse.coefficientMatrix mu
              (Stage9C.Material.SpinPair.actual.coframe 0) *
              connectionDirection (sourceField g) mu := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro mu _
      rw [sourceField_conn_add, mul_add]
    rw [sumSplit, sourceField_scalar_add]
    simp only [smul_add]
    ac_rfl
  · simp only [add_zero]

theorem fieldDensityCoefficients_smul (r : ℝ) (f : Field289) (i : Fin 4) :
    fieldDensityCoefficients (sourceField (r • f)) i =
      r • fieldDensityCoefficients (sourceField f) i := by
  unfold fieldDensityCoefficients
  rw [sourceField_coframe_smul, coframeDensityCoefficients_smul]
  split_ifs with h
  · have sumScale : (∑ mu : Fin 4,
          FullQuantum.CoframeResponse.coefficientMatrix mu
            (Stage9C.Material.SpinPair.actual.coframe 0) *
            connectionDirection (sourceField (r • f)) mu) =
        (r : ℂ) • ∑ mu : Fin 4,
          FullQuantum.CoframeResponse.coefficientMatrix mu
            (Stage9C.Material.SpinPair.actual.coframe 0) *
            connectionDirection (sourceField f) mu := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro mu _
      rw [sourceField_conn_smul,
        RCLike.real_smul_eq_coe_smul (K := ℂ) r
          (connectionDirection (sourceField f) mu)]
      exact mul_smul_comm (r : ℂ) _ _
    rw [sumScale, sourceField_scalar_smul]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp only [smul_add]
    simp only [smul_comm sourceVolume]
    ac_rfl
  · simp only [add_zero]

/-- The original fiber coefficients `fieldCoefficients (sourceField f) i` are
    real-linear in the 289-field. -/
def realDensityCoefficients (i : Fin 4) : Field289 →ₗ[ℝ] FiberOperators where
  toFun := fun f => fieldCoefficients (sourceField f) i
  map_add' := fun f g => by
    simp only [fieldCoefficients]
    rw [fieldDensityCoefficients_add, map_add]
  map_smul' := fun r f => by
    simp only [fieldCoefficients]
    rw [fieldDensityCoefficients_smul, RingHom.id_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ) r
        (fieldDensityCoefficients (sourceField f) i), map_smul]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) r
      (canonicalMatrixRead (fieldDensityCoefficients (sourceField f) i))).symm

/-- The original Hamiltonian coefficients `frequencyCoefficients
    (sourceField f) i` are real-linear in the 289-field. -/
def realFrequencyCoefficients (i : Fin 4) : Field289 →ₗ[ℝ] FiberOperators where
  toFun := fun f => frequencyCoefficients (sourceField f) i
  map_add' := fun f g => by
    simp only [frequencyCoefficients, fieldHamiltonianCoefficients]
    rw [fieldDensityCoefficients_add, mul_add, smul_add]
    simp only [map_add, operator_add]
  map_smul' := fun r f => by
    simp only [frequencyCoefficients, fieldHamiltonianCoefficients]
    rw [fieldDensityCoefficients_smul, RingHom.id_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ) r
        (fieldDensityCoefficients (sourceField f) i), mul_smul_comm,
      smul_comm (-Complex.I * sourceVolume⁻¹), map_smul, operator_smul]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) r
      (frequencyCoefficients (sourceField f) i)).symm

/-- The density coefficients are continuous because the domain is a
    finite-dimensional real space. -/
def realDensityCoefficientsContinuous (i : Fin 4) : Field289 →L[ℝ] FiberOperators :=
  (realDensityCoefficients i).toContinuousLinearMap

/-- The frequency coefficients are continuous for the same reason. -/
def realFrequencyCoefficientsContinuous (i : Fin 4) : Field289 →L[ℝ] FiberOperators :=
  (realFrequencyCoefficients i).toContinuousLinearMap

/-- Contract A read-back: the real density map evaluates to the original
    source field coefficients. -/
theorem realDensityCoefficients_source (f : Field289) (i : Fin 4) :
    realDensityCoefficients i f = fieldCoefficients (sourceField f) i := rfl

theorem realFrequencyCoefficients_source (f : Field289) (i : Fin 4) :
    realFrequencyCoefficients i f = frequencyCoefficients (sourceField f) i := rfl

end LowEnergy.GaussComposite.PhysicalFullFieldScattering
