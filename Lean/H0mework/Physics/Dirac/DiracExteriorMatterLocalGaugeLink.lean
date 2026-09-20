import H0mework.Physics.Dirac.DiracExteriorMatterAction

/-!
# Endpoint-local finite transport for actual Dirac exterior matter

This module closes the finite-link part of Stage 8A without reinterpreting the
Stage-6 connection jet as a continuum covariant derivative.  The matrix
`1 + A_mu` is treated as a general linear source-to-target transporter.  It
need not itself be an element of SU(7).  Independent source and target SU(7)
gauges act by

`U_mu |-> g_source U_mu g_target(mu)^*`,

and exterior-power functoriality proves exact endpoint-local covariance on the
actual Stage-7 carrier `Λ⁶V ⊕ Λ²V ⊕ Λ⁴V`.  The finite link residual is based at
the source, where the coframe-generated Dirac spin connection is added.  The
spin and internal actions commute, so the joint derivative is locally SU(7)
covariant and its dual-paired density is invariant.

The same Stage-6 mother potential generates every link; gamma/coframe
compatibility still comes from the generated tetrad postulate.  Positive and
constant-field regressions exclude an identically-zero density and a spurious
identity-link residual.

Boundary: this is a pointwise first-jet/finite-link theorem.  It is not a
smooth principal bundle, a path-ordered exponential, a global spin structure,
or a proof of arbitrary finite local Spin(1,3) chart descent.
-/

namespace SaturationMonoid.PhysicsCore.DiracExteriorMatterLocalGaugeLink

open Matrix
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open SU7MotherLieAlgebra
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterGaugeCovariantJet
open DiracExteriorMatterAction
open SU7MotherGaugeTheory

open scoped TensorProduct

noncomputable section

abbrev SU7MotherFundamentalLink :=
  Matrix SU7MotherIndex SU7MotherIndex ℂ

def motherFundamentalLinkOfPotential
    (potential : SU7MotherLieMatrix) : SU7MotherFundamentalLink :=
  1 + (potential : Matrix SU7MotherIndex SU7MotherIndex ℂ)

def fundamentalLinkAction (link : SU7MotherFundamentalLink) :
    Module.End ℂ SU7FundamentalCarrier :=
  Matrix.mulVecLin link

def gaugeTransformFundamentalLink
    (sourceGauge targetGauge : SU7MotherGroup)
    (link : SU7MotherFundamentalLink) : SU7MotherFundamentalLink :=
  (sourceGauge : Matrix SU7MotherIndex SU7MotherIndex ℂ) * link *
    star (targetGauge : Matrix SU7MotherIndex SU7MotherIndex ℂ)

theorem gaugeTransformFundamentalLink_mul_target
    (sourceGauge targetGauge : SU7MotherGroup)
    (link : SU7MotherFundamentalLink) :
    gaugeTransformFundamentalLink sourceGauge targetGauge link *
        (targetGauge : Matrix SU7MotherIndex SU7MotherIndex ℂ) =
      (sourceGauge : Matrix SU7MotherIndex SU7MotherIndex ℂ) * link := by
  have htarget :
      star (targetGauge : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
          (targetGauge : Matrix SU7MotherIndex SU7MotherIndex ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp
      (Matrix.specialUnitaryGroup_le_unitaryGroup targetGauge.property)
  rw [gaugeTransformFundamentalLink]
  calc
    ((sourceGauge : Matrix SU7MotherIndex SU7MotherIndex ℂ) * link *
          star (targetGauge : Matrix SU7MotherIndex SU7MotherIndex ℂ)) *
        (targetGauge : Matrix SU7MotherIndex SU7MotherIndex ℂ) =
      (sourceGauge : Matrix SU7MotherIndex SU7MotherIndex ℂ) * link *
        (star (targetGauge : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
          (targetGauge : Matrix SU7MotherIndex SU7MotherIndex ℂ)) := by
        noncomm_ring
    _ = _ := by rw [htarget, Matrix.mul_one]

theorem fundamentalLinkAction_localGauge_covariant
    (sourceGauge targetGauge : SU7MotherGroup)
    (link : SU7MotherFundamentalLink) :
    (fundamentalLinkAction
        (gaugeTransformFundamentalLink sourceGauge targetGauge link)).comp
          (su7FundamentalRepresentation targetGauge) =
      (su7FundamentalRepresentation sourceGauge).comp
        (fundamentalLinkAction link) := by
  apply LinearMap.ext
  intro vector
  change
    gaugeTransformFundamentalLink sourceGauge targetGauge link *ᵥ
        ((targetGauge : Matrix SU7MotherIndex SU7MotherIndex ℂ) *ᵥ vector) =
      (sourceGauge : Matrix SU7MotherIndex SU7MotherIndex ℂ) *ᵥ
        (link *ᵥ vector)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    gaugeTransformFundamentalLink_mul_target]

def exteriorLinkAction (degree : ℕ) (link : SU7MotherFundamentalLink) :
    Module.End ℂ (⋀[ℂ]^degree SU7FundamentalCarrier) :=
  exteriorPower.map degree (fundamentalLinkAction link)

theorem exteriorLinkAction_localGauge_covariant
    (degree : ℕ) (sourceGauge targetGauge : SU7MotherGroup)
    (link : SU7MotherFundamentalLink) :
    (exteriorLinkAction degree
        (gaugeTransformFundamentalLink sourceGauge targetGauge link)).comp
          (su7ExteriorPowerRepresentation degree targetGauge) =
      (su7ExteriorPowerRepresentation degree sourceGauge).comp
        (exteriorLinkAction degree link) := by
  change
    (exteriorPower.map degree
        (fundamentalLinkAction
          (gaugeTransformFundamentalLink sourceGauge targetGauge link))).comp
          (exteriorPower.map degree
            (su7FundamentalRepresentation targetGauge)) =
      (exteriorPower.map degree
          (su7FundamentalRepresentation sourceGauge)).comp
        (exteriorPower.map degree (fundamentalLinkAction link))
  rw [← exteriorPower.map_comp, ← exteriorPower.map_comp,
    fundamentalLinkAction_localGauge_covariant]

def exteriorSpinorLinkAction (link : SU7MotherFundamentalLink) :
    Module.End ℂ SU7ExteriorSpinorMatterCarrier :=
  (exteriorLinkAction 6 link).prodMap
    ((exteriorLinkAction 2 link).prodMap
      (exteriorLinkAction 4 link))

theorem exteriorSpinorLinkAction_localGauge_covariant
    (sourceGauge targetGauge : SU7MotherGroup)
    (link : SU7MotherFundamentalLink) :
    (exteriorSpinorLinkAction
        (gaugeTransformFundamentalLink sourceGauge targetGauge link)).comp
          (su7ExteriorSpinorMatterRepresentation targetGauge) =
      (su7ExteriorSpinorMatterRepresentation sourceGauge).comp
        (exteriorSpinorLinkAction link) := by
  apply LinearMap.ext
  rintro ⟨degreeSix, degreeTwo, degreeFour⟩
  apply Prod.ext
  · simpa [exteriorSpinorLinkAction,
      su7ExteriorSpinorMatterRepresentation] using
      LinearMap.congr_fun
        (exteriorLinkAction_localGauge_covariant 6 sourceGauge targetGauge link)
        degreeSix
  · apply Prod.ext
    · simpa [exteriorSpinorLinkAction,
        su7ExteriorSpinorMatterRepresentation] using
        LinearMap.congr_fun
          (exteriorLinkAction_localGauge_covariant 2 sourceGauge targetGauge link)
          degreeTwo
    · simpa [exteriorSpinorLinkAction,
        su7ExteriorSpinorMatterRepresentation] using
        LinearMap.congr_fun
          (exteriorLinkAction_localGauge_covariant 4 sourceGauge targetGauge link)
          degreeFour

theorem exteriorSpinorLinkAction_of_motherPotential
    (potential : SU7MotherLieMatrix) :
    exteriorSpinorLinkAction (motherFundamentalLinkOfPotential potential) =
      exteriorSpinorMotherTransport potential := by
  rfl

def diracExteriorLinkAction (link : SU7MotherFundamentalLink) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  internalMatterLinearAction (exteriorSpinorLinkAction link)

theorem diracExteriorLinkAction_localGauge_covariant
    (sourceGauge targetGauge : SU7MotherGroup)
    (link : SU7MotherFundamentalLink) :
    (diracExteriorLinkAction
        (gaugeTransformFundamentalLink sourceGauge targetGauge link)).comp
          (diracExteriorMatterGaugeRepresentation targetGauge) =
      (diracExteriorMatterGaugeRepresentation sourceGauge).comp
        (diracExteriorLinkAction link) := by
  apply LinearMap.ext
  intro field
  funext spinIndex
  exact LinearMap.congr_fun
    (exteriorSpinorLinkAction_localGauge_covariant
      sourceGauge targetGauge link) (field spinIndex)

structure DiracExteriorMatterLinkJet where
  sourceField : DiracExteriorMatterCarrier
  targetField : LorentzianIndex → DiracExteriorMatterCarrier
  sourceConjugateField : Module.Dual ℂ DiracExteriorMatterCarrier

structure LocalSU7GaugeJet where
  sourceGauge : SU7MotherGroup
  targetGauge : LorentzianIndex → SU7MotherGroup

def motherLinkFamilyOfConnection
    (connection : SU7MotherGaugeConnection) :
    LorentzianIndex → SU7MotherFundamentalLink :=
  fun direction =>
    motherFundamentalLinkOfPotential (connection.potential direction)

def localGaugeTransformLinkFamily
    (gauge : LocalSU7GaugeJet)
    (links : LorentzianIndex → SU7MotherFundamentalLink) :
    LorentzianIndex → SU7MotherFundamentalLink :=
  fun direction =>
    gaugeTransformFundamentalLink gauge.sourceGauge
      (gauge.targetGauge direction) (links direction)

def localGaugeTransformMatterLinkJet
    (gauge : LocalSU7GaugeJet)
    (jet : DiracExteriorMatterLinkJet) : DiracExteriorMatterLinkJet where
  sourceField :=
    diracExteriorMatterGaugeRepresentation gauge.sourceGauge jet.sourceField
  targetField := fun direction =>
    diracExteriorMatterGaugeRepresentation (gauge.targetGauge direction)
      (jet.targetField direction)
  sourceConjugateField := jet.sourceConjugateField.comp
    (diracExteriorMatterGaugeRepresentation gauge.sourceGauge⁻¹)

def diracExteriorMatterLinkResidual
    (links : LorentzianIndex → SU7MotherFundamentalLink)
    (jet : DiracExteriorMatterLinkJet)
    (direction : LorentzianIndex) : DiracExteriorMatterCarrier :=
  diracExteriorLinkAction (links direction) (jet.targetField direction) -
    jet.sourceField

theorem diracExteriorMatterLinkResidual_localGauge_covariant
    (gauge : LocalSU7GaugeJet)
    (links : LorentzianIndex → SU7MotherFundamentalLink)
    (jet : DiracExteriorMatterLinkJet)
    (direction : LorentzianIndex) :
    diracExteriorMatterLinkResidual
        (localGaugeTransformLinkFamily gauge links)
        (localGaugeTransformMatterLinkJet gauge jet) direction =
      diracExteriorMatterGaugeRepresentation gauge.sourceGauge
        (diracExteriorMatterLinkResidual links jet direction) := by
  have htransport := LinearMap.congr_fun
    (diracExteriorLinkAction_localGauge_covariant gauge.sourceGauge
      (gauge.targetGauge direction) (links direction))
    (jet.targetField direction)
  simpa [diracExteriorMatterLinkResidual,
    localGaugeTransformLinkFamily, localGaugeTransformMatterLinkJet,
    map_sub] using htransport

def diracExteriorMatterJointLinkDerivative
    (geometry : PointwiseLorentzianCoframeJet)
    (links : LorentzianIndex → SU7MotherFundamentalLink)
    (jet : DiracExteriorMatterLinkJet)
    (direction : LorentzianIndex) : DiracExteriorMatterCarrier :=
  diracExteriorMatterLinkResidual links jet direction +
    diracSpinConnectionMatterAction geometry direction jet.sourceField

theorem diracExteriorMatterJointLinkDerivative_localGauge_covariant
    (gauge : LocalSU7GaugeJet)
    (geometry : PointwiseLorentzianCoframeJet)
    (links : LorentzianIndex → SU7MotherFundamentalLink)
    (jet : DiracExteriorMatterLinkJet)
    (direction : LorentzianIndex) :
    diracExteriorMatterJointLinkDerivative geometry
        (localGaugeTransformLinkFamily gauge links)
        (localGaugeTransformMatterLinkJet gauge jet) direction =
      diracExteriorMatterGaugeRepresentation gauge.sourceGauge
        (diracExteriorMatterJointLinkDerivative geometry links jet direction) := by
  have hresidual :=
    diracExteriorMatterLinkResidual_localGauge_covariant
      gauge links jet direction
  have hspin := LinearMap.congr_fun
    (diracMatrixMatterAction_commutes_internal
      (diracSpinConnectionLift geometry.lorentzSpinConnection direction)
      (su7ExteriorSpinorMatterRepresentation gauge.sourceGauge))
    jet.sourceField
  rw [diracExteriorMatterJointLinkDerivative,
    diracExteriorMatterJointLinkDerivative, map_add]
  rw [hresidual]
  exact congrArg
    (fun value =>
      diracExteriorMatterGaugeRepresentation gauge.sourceGauge
          (diracExteriorMatterLinkResidual links jet direction) + value)
    hspin

def diracExteriorMatterLinkKineticVector
    (geometry : PointwiseLorentzianCoframeJet)
    (links : LorentzianIndex → SU7MotherFundamentalLink)
    (jet : DiracExteriorMatterLinkJet) : DiracExteriorMatterCarrier :=
  Complex.I •
    ∑ direction : LorentzianIndex,
      diracMatrixMatterAction (inverseCoframeDiracGamma geometry direction)
        (diracExteriorMatterJointLinkDerivative geometry links jet direction)

theorem diracExteriorMatterLinkKineticVector_localGauge_covariant
    (gauge : LocalSU7GaugeJet)
    (geometry : PointwiseLorentzianCoframeJet)
    (links : LorentzianIndex → SU7MotherFundamentalLink)
    (jet : DiracExteriorMatterLinkJet) :
    diracExteriorMatterLinkKineticVector geometry
        (localGaugeTransformLinkFamily gauge links)
        (localGaugeTransformMatterLinkJet gauge jet) =
      diracExteriorMatterGaugeRepresentation gauge.sourceGauge
        (diracExteriorMatterLinkKineticVector geometry links jet) := by
  rw [diracExteriorMatterLinkKineticVector,
    diracExteriorMatterLinkKineticVector, map_smul, map_sum]
  apply congrArg (fun field => Complex.I • field)
  apply Finset.sum_congr rfl
  intro direction _
  rw [diracExteriorMatterJointLinkDerivative_localGauge_covariant]
  exact LinearMap.congr_fun
    (diracMatrixMatterAction_commutes_internal
      (inverseCoframeDiracGamma geometry direction)
      (su7ExteriorSpinorMatterRepresentation gauge.sourceGauge))
    (diracExteriorMatterJointLinkDerivative geometry links jet direction)

theorem diracExteriorMatterJointLink_geometryGammaCompatible
    (geometry : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det geometry.coframe ≠ 0)
    (direction coordinate : LorentzianIndex) :
    coframeDiracGammaCovariantDerivative geometry direction coordinate = 0 :=
  coframeDiracGammaCovariantDerivative_eq_zero geometry hcoframe
    direction coordinate

def diracExteriorMatterLinkActionDensity
    (geometry : PointwiseLorentzianCoframeJet)
    (links : LorentzianIndex → SU7MotherFundamentalLink)
    (jet : DiracExteriorMatterLinkJet) : ℂ :=
  ((abs (Matrix.det geometry.coframe) : ℝ) : ℂ) *
    jet.sourceConjugateField
      (diracExteriorMatterLinkKineticVector geometry links jet)

theorem diracExteriorMatterLinkActionDensity_localGauge_invariant
    (gauge : LocalSU7GaugeJet)
    (geometry : PointwiseLorentzianCoframeJet)
    (links : LorentzianIndex → SU7MotherFundamentalLink)
    (jet : DiracExteriorMatterLinkJet) :
    diracExteriorMatterLinkActionDensity geometry
        (localGaugeTransformLinkFamily gauge links)
        (localGaugeTransformMatterLinkJet gauge jet) =
      diracExteriorMatterLinkActionDensity geometry links jet := by
  rw [diracExteriorMatterLinkActionDensity,
    diracExteriorMatterLinkActionDensity,
    diracExteriorMatterLinkKineticVector_localGauge_covariant]
  simp [localGaugeTransformMatterLinkJet]

theorem diracExteriorMatterLinkAction_uses_same_motherConnection
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (jet : DiracExteriorMatterLinkJet) :
    diracExteriorMatterLinkActionDensity geometry
        (motherLinkFamilyOfConnection connection) jet =
      diracExteriorMatterLinkActionDensity geometry
        (fun direction =>
          1 + (connection.potential direction :
            Matrix SU7MotherIndex SU7MotherIndex ℂ)) jet := by
  rfl

/-! ## Positive and constant-field regressions -/

def identityFundamentalLinkFamily :
    LorentzianIndex → SU7MotherFundamentalLink :=
  fun _ => 1

@[simp] theorem diracExteriorLinkAction_one :
    diracExteriorLinkAction (1 : SU7MotherFundamentalLink) =
      LinearMap.id := by
  apply LinearMap.ext
  intro field
  funext spinIndex
  rcases field spinIndex with ⟨degreeSix, degreeTwo, degreeFour⟩
  apply Prod.ext
  · simp [diracExteriorLinkAction, internalMatterLinearAction,
      exteriorSpinorLinkAction, exteriorLinkAction, fundamentalLinkAction]
  · apply Prod.ext <;>
      simp [diracExteriorLinkAction, internalMatterLinearAction,
        exteriorSpinorLinkAction, exteriorLinkAction, fundamentalLinkAction]

def nonzeroLocalLinkMatterJet : DiracExteriorMatterLinkJet where
  sourceField := 0
  targetField := fun direction =>
    if direction = 0 then diracSpinTwoMatterProbe else 0
  sourceConjugateField := diracSpinZeroMatterCoordinate

theorem nonzeroLocalLinkMatterJet_jointDerivative
    (direction : LorentzianIndex) :
    diracExteriorMatterJointLinkDerivative identityCoframeMatterGeometry
        identityFundamentalLinkFamily nonzeroLocalLinkMatterJet direction =
      if direction = 0 then diracSpinTwoMatterProbe else 0 := by
  simp [diracExteriorMatterJointLinkDerivative,
    diracExteriorMatterLinkResidual, identityFundamentalLinkFamily,
    nonzeroLocalLinkMatterJet, diracSpinConnectionMatterAction]

theorem nonzeroLocalLinkMatterJet_kineticVector :
    diracExteriorMatterLinkKineticVector identityCoframeMatterGeometry
        identityFundamentalLinkFamily nonzeroLocalLinkMatterJet =
      Complex.I • diracSpinZeroMatterProbe := by
  rw [diracExteriorMatterLinkKineticVector]
  simp only [inverseCoframeDiracGamma_identity,
    nonzeroLocalLinkMatterJet_jointDerivative, Fin.sum_univ_four]
  simp [diracGamma,
    show (1 : LorentzianIndex) ≠ 0 by decide,
    show (2 : LorentzianIndex) ≠ 0 by decide,
    show (3 : LorentzianIndex) ≠ 0 by decide]
  rw [diracGammaZero_maps_spinTwoProbe]

/-- Positive regression: endpoint-local covariance has not made the finite
matter density identically zero. -/
theorem nonzeroLocalLinkMatterJet_actionDensity :
    diracExteriorMatterLinkActionDensity identityCoframeMatterGeometry
        identityFundamentalLinkFamily nonzeroLocalLinkMatterJet =
      Complex.I := by
  rw [diracExteriorMatterLinkActionDensity,
    nonzeroLocalLinkMatterJet_kineticVector]
  simp [identityCoframeMatterGeometry, nonzeroLocalLinkMatterJet]

def constantLocalLinkMatterJet
    (field : DiracExteriorMatterCarrier) : DiracExteriorMatterLinkJet where
  sourceField := field
  targetField := fun _ => field
  sourceConjugateField := 0

/-- Negative regression: a constant field across an identity link has no
internal link residual. -/
@[simp] theorem constantLocalLinkMatterJet_residual
    (field : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    diracExteriorMatterLinkResidual identityFundamentalLinkFamily
        (constantLocalLinkMatterJet field) direction = 0 := by
  simp [diracExteriorMatterLinkResidual, identityFundamentalLinkFamily,
    constantLocalLinkMatterJet]

/-! ## Proof-only Stage-8A receipt -/

/-- A dependency-light receipt for the finite Stage-8A jurisdiction.  Its
proof fields are consequences of the actual constructions above; it is not a
physical-admission credential and carries no lineage or phenomenology claim. -/
structure StageEightACovariantMatterReceipt where
  geometry : PointwiseLorentzianCoframeJet
  motherConnection : SU7MotherGaugeConnection
  matterJet : DiracExteriorMatterLinkJet
  coframeNondegenerate : Matrix.det geometry.coframe ≠ 0
  localGaugeInvariant : ∀ gauge : LocalSU7GaugeJet,
    diracExteriorMatterLinkActionDensity geometry
        (localGaugeTransformLinkFamily gauge
          (motherLinkFamilyOfConnection motherConnection))
        (localGaugeTransformMatterLinkJet gauge matterJet) =
      diracExteriorMatterLinkActionDensity geometry
        (motherLinkFamilyOfConnection motherConnection) matterJet
  geometryGammaCompatible : ∀ direction coordinate : LorentzianIndex,
    coframeDiracGammaCovariantDerivative geometry direction coordinate = 0
  usesSameMotherConnection :
    diracExteriorMatterLinkActionDensity geometry
        (motherLinkFamilyOfConnection motherConnection) matterJet =
      diracExteriorMatterLinkActionDensity geometry
        (fun direction =>
          1 + (motherConnection.potential direction :
            Matrix SU7MotherIndex SU7MotherIndex ℂ)) matterJet
  nonzeroDensity :
    diracExteriorMatterLinkActionDensity geometry
        (motherLinkFamilyOfConnection motherConnection) matterJet ≠ 0

theorem zeroMotherLinkFamily_eq_identity :
    motherLinkFamilyOfConnection zeroMotherGaugeConnection =
      identityFundamentalLinkFamily := by
  funext direction
  simp [motherLinkFamilyOfConnection, motherFundamentalLinkOfPotential,
    zeroMotherGaugeConnection, identityFundamentalLinkFamily]

def stageEightACovariantMatterReceipt :
    StageEightACovariantMatterReceipt where
  geometry := identityCoframeMatterGeometry
  motherConnection := zeroMotherGaugeConnection
  matterJet := nonzeroLocalLinkMatterJet
  coframeNondegenerate := by
    simp [identityCoframeMatterGeometry]
  localGaugeInvariant := fun gauge =>
    diracExteriorMatterLinkActionDensity_localGauge_invariant gauge
      identityCoframeMatterGeometry
      (motherLinkFamilyOfConnection zeroMotherGaugeConnection)
      nonzeroLocalLinkMatterJet
  geometryGammaCompatible := fun direction coordinate =>
    diracExteriorMatterJointLink_geometryGammaCompatible
      identityCoframeMatterGeometry (by simp [identityCoframeMatterGeometry])
      direction coordinate
  usesSameMotherConnection :=
    diracExteriorMatterLinkAction_uses_same_motherConnection
      identityCoframeMatterGeometry zeroMotherGaugeConnection
      nonzeroLocalLinkMatterJet
  nonzeroDensity := by
    rw [zeroMotherLinkFamily_eq_identity,
      nonzeroLocalLinkMatterJet_actionDensity]
    exact Complex.I_ne_zero

end
end SaturationMonoid.PhysicsCore.DiracExteriorMatterLocalGaugeLink
