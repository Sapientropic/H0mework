import H0mework.Physics.JointSources.P408

/-!
# Proposition 409: finite physical alpha-RG steps produce the single-source receipt

P404 is the current Standard-Model grand-unification front door, but its scale
relation is still an abstract physical relation.  This file lowers that
remaining producer to the shape a concrete RG / threshold calculation can
actually emit:

* a local finite RG step relation;
* selected Yukawa paths to the weak endpoint in the reflexive-transitive
  closure of those steps;
* local monotonicity of the physical alpha `g^2/(4*pi)` on every step;
* a certificate that the generated reachability relation is not merely the
  target alpha-order predicate in disguise.

Lean then extends local alpha monotonicity along finite paths, constructs the
P404 physical alpha-RG monotonicity producer, and immediately transports it to
P408's single-source holy-grail receipt.

Boundary: this still does not derive the beta functions, threshold matching, or
SU(7) representation content.  It identifies the smaller finite path
certificate those calculations must supply.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Finite physical alpha-RG step producer -/

/-- A concrete physical RG-step producer in alpha coordinates.

The anti-tautology field is on the generated reachability relation, not merely
on the raw local edge predicate.  This is the point that keeps the path
certificate from collapsing back to the alpha-order target after taking
transitive closure. -/
structure PhysicalAlphaRGStepPathProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
  step : StandardModelScaleCode -> StandardModelScaleCode -> Prop
  reach_not_alpha_order :
    RGStepReach step ≠
      fun a b : StandardModelScaleCode =>
        alphaFromGaugeCoupling realFourPi (Z.running.gaugeCoupling a) ≤
          alphaFromGaugeCoupling realFourPi (Z.running.gaugeCoupling b)
  fourPi_eq_realFourPi : Z.running.fourPi = realFourPi
  selected_yukawa_reaches_weak :
    ∀ y : YukawaParameter,
      RGStepReach step (StandardModelScaleCode.yukawa y)
        StandardModelScaleCode.weak
  step_alpha_monotone :
    ∀ {a b : StandardModelScaleCode}, step a b ->
      alphaFromGaugeCoupling realFourPi (Z.running.gaugeCoupling a) ≤
        alphaFromGaugeCoupling realFourPi (Z.running.gaugeCoupling b)

namespace PhysicalAlphaRGStepPathProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- THEOREM 1: local physical-alpha monotonicity extends along finite RG
reachability. -/
theorem alpha_monotone_of_reach
    (C : PhysicalAlphaRGStepPathProducer Z)
    {a b : StandardModelScaleCode} :
    RGStepReach C.step a b ->
      alphaFromGaugeCoupling realFourPi (Z.running.gaugeCoupling a) ≤
        alphaFromGaugeCoupling realFourPi (Z.running.gaugeCoupling b) := by
  intro h
  induction h with
  | refl =>
      exact le_rfl
  | tail hreach hbc ih =>
      exact le_trans ih (C.step_alpha_monotone hbc)

/-- THEOREM 2: a finite physical alpha-step table is exactly a concrete
producer for P404's physical alpha-RG monotonicity surface. -/
def toPhysicalAlphaRGMonotonicityProducer
    (C : PhysicalAlphaRGStepPathProducer Z) :
    PhysicalAlphaRGMonotonicityProducer Z :=
  { physicalScaleLe := RGStepReach C.step
    scale_relation_not_alpha_order := C.reach_not_alpha_order
    fourPi_eq_realFourPi := C.fourPi_eq_realFourPi
    selected_yukawa_le_weak := C.selected_yukawa_reaches_weak
    alpha_monotone := fun h => C.alpha_monotone_of_reach h }

end PhysicalAlphaRGStepPathProducer

/-! ## Existence-level bridges into the holy-grail receipt -/

/-- A zero-free certificate equipped with the finite physical alpha-RG step
producer. -/
def ExistsZeroFreePhysicalAlphaRGStepPathProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (PhysicalAlphaRGStepPathProducer Z)

/-- THEOREM 3: finite physical alpha-RG paths supply the P404 front door. -/
theorem existsZeroFreePhysicalAlphaRGMonotonicityProducer_of_alphaRGStepPath
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalAlphaRGStepPathProducer Index A CKMCarrier ->
      ExistsZeroFreePhysicalAlphaRGMonotonicityProducer Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, ⟨C.toPhysicalAlphaRGMonotonicityProducer⟩⟩

/-- THEOREM 4: finite physical alpha-RG paths supply P407's single-source
producer through the P408 equivalence. -/
theorem existsSingleSourcePhysicalGrandUnificationProducer_of_alphaRGStepPath
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalAlphaRGStepPathProducer Index A CKMCarrier ->
      ExistsSingleSourcePhysicalGrandUnificationProducer Index A CKMCarrier :=
  singleSourcePhysicalProducer_of_physicalAlphaRGMonotonicity ∘
    existsZeroFreePhysicalAlphaRGMonotonicityProducer_of_alphaRGStepPath

/-- THEOREM 5: finite physical alpha-RG paths are sufficient for the canonical
single-source holy-grail receipt to exist. -/
theorem singleSourcePhysicalHolyGrailReceipt_nonempty_of_alphaRGStepPath
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalAlphaRGStepPathProducer Index A CKMCarrier ->
      Nonempty (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
        Index A CKMCarrier) := by
  intro h
  exact
    singleSourcePhysicalHolyGrailReceipt_nonempty_of_producer
      (existsSingleSourcePhysicalGrandUnificationProducer_of_alphaRGStepPath h)

/-- THEOREM 6: compact holy-grail receipt from the finite physical alpha-RG
step certificate. -/
theorem physicalAlphaRGStepPath_singleSource_holy_grail_receipt
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalAlphaRGStepPathProducer Index A CKMCarrier ->
      ∃ C : SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier,
        C.receipt.zeroFree = C.atoms.toZeroFree ∧
        HEq C.receipt.rg
          C.physicalRG.toSelectedYukawaRGMonotonicityCertificate ∧
        C.receipt.spine = C.atoms.toUnifiedFormulaSpine ∧
        C.receipt.primitiveAtoms = C.atoms ∧
        C.receipt.spine.target.sampled.zeroFree = C.atoms.toZeroFree ∧
        alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
        gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
        alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
        C.receipt.spine.target.strongResidualProducer.correctedOutput =
          alphaStrongDisplayed ℝ ∧
        (ckmCPDepthSum : ℝ) * C.receipt.spine.target.cpRunningSigma =
          cpRawPhaseClaim ℝ := by
  intro h
  exact
    physicalAlphaRGMonotonicity_singleSource_holy_grail_receipt
      (existsZeroFreePhysicalAlphaRGMonotonicityProducer_of_alphaRGStepPath h)

end StandardModelConstraint
end SaturationMonoid
