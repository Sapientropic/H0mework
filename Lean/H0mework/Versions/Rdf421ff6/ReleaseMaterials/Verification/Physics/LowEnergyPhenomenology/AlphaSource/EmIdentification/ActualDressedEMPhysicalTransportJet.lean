import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMSourceTangentClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMSourceTransport
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMQuantumThreshold ActualDressedEMClockDispersion
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] correctedPhysicalClock physicalQuantumResponse

def sourceTangentRead (P : TangentFrequency) (t : ℝ) (s : ℂ) : ℂ :=
  (tangentFrequencySpecialize t P).eval s

def sourceTangentSpatialPolynomial (P : TangentFrequency) (s : ℂ) : ℂ[X] := P.eval (C s)

theorem actual_source_tangent_read (P : TangentFrequency) (t : ℝ) (s : ℂ) :
    sourceTangentRead P t s=(sourceTangentSpatialPolynomial P s).eval (t : ℂ) := by
  simpa only [sourceTangentRead,sourceTangentSpatialPolynomial,tangentFrequencySpecialize,
    Polynomial.coe_mapRingHom,coe_evalRingHom,eval_C] using
      (eval_map_apply (p:=P) (evalRingHom (t : ℂ)) (C s))

def sourceTangentPhysicalPencil (event : DressedEvent) (eps omega t : ℝ) (n delta : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ := fun i j =>
  sourceTangentRead (sourceTangentThresholdPencil event eps n delta i j) t ((omega/eps^2 : ℝ) : ℂ)/
    sourceTangentRead (sourceTangentThresholdClearing event eps n delta) t ((omega/eps^2 : ℝ) : ℂ)

def sourceTangentPhysicalSpatialJet (event : DressedEvent) (eps omega : ℝ) (n delta : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ := fun i j =>
  let N := sourceTangentSpatialPolynomial (sourceTangentThresholdPencil event eps n delta i j) ((omega/eps^2 : ℝ) : ℂ)
  let d := sourceTangentSpatialPolynomial (sourceTangentThresholdClearing event eps n delta) ((omega/eps^2 : ℝ) : ℂ)
  (N.derivative.eval 0*d.eval 0-N.eval 0*d.derivative.eval 0)/(d.eval 0)^2

/-- Same source open chart fixes damping order and returns the complete actual corrected operator. -/
theorem actual_source_tangent_physical_pencil (event : DressedEvent) (eps omega t : ℝ) (n delta : PhysicalMomentum)
    (eps_ne : eps≠0)
    (regular : sourceTangentRead (sourceTangentThresholdClearing event eps n delta) t ((omega/eps^2 : ℝ) : ℂ)≠0) :
    sourceTangentPhysicalPencil event eps omega t n delta=
      correctedPhysicalClock event eps omega (sourceTangentMomentum n delta t) := by
  have polynomialRegular : tangentFrequencySpecialize t (sourceTangentThresholdClearing event eps n delta)≠0 := by
    intro vanish
    exact regular (by simp [sourceTangentRead,vanish])
  have clearing := actual_tangent_threshold_clearing event eps t n delta polynomialRegular
  have oldRegular : (zeroClockClearing event eps (sourceTangentMomentum n delta t)).eval ((omega/eps^2 : ℝ) : ℂ)≠0 := by
    rw [←clearing]
    exact regular
  rw [actual_corrected_physical_threshold event eps omega (sourceTangentMomentum n delta t) eps_ne oldRegular]
  have pencil := actual_tangent_threshold_pencil event eps t n delta polynomialRegular
  funext i j
  change sourceTangentRead _ t _/sourceTangentRead _ t _=
    (zeroClockPencil event eps (sourceTangentMomentum n delta t) i j).eval _/
      (zeroClockClearing event eps (sourceTangentMomentum n delta t)).eval _
  rw [sourceTangentRead,sourceTangentRead,clearing]
  exact congrArg (fun P : ℂ[X] => P.eval ((omega/eps^2 : ℝ) : ℂ)/
    (zeroClockClearing event eps (sourceTangentMomentum n delta t)).eval ((omega/eps^2 : ℝ) : ℂ))
      (congrFun (congrFun pencil i) j)

/-- Space differentiation retains d' and every full Q/background/lower component. -/
theorem actual_source_tangent_spatial_derivative (event : DressedEvent) (eps omega : ℝ) (n delta : PhysicalMomentum)
    (regular : sourceTangentRead (sourceTangentThresholdClearing event eps n delta) 0 ((omega/eps^2 : ℝ) : ℂ)≠0) :
    HasDerivAt (fun t : ℝ => sourceTangentPhysicalPencil event eps omega t n delta)
      (sourceTangentPhysicalSpatialJet event eps omega n delta) 0 := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have chart : (sourceTangentSpatialPolynomial (sourceTangentThresholdClearing event eps n delta)
      ((omega/eps^2 : ℝ) : ℂ)).eval 0≠0 := by
    simpa only [actual_source_tangent_read,Complex.ofReal_zero] using regular
  have generated := ((sourceTangentSpatialPolynomial (sourceTangentThresholdPencil event eps n delta i j)
    ((omega/eps^2 : ℝ) : ℂ)).hasDerivAt (0 : ℂ)).div
      ((sourceTangentSpatialPolynomial (sourceTangentThresholdClearing event eps n delta)
        ((omega/eps^2 : ℝ) : ℂ)).hasDerivAt (0 : ℂ)) chart
  simpa only [sourceTangentPhysicalPencil,actual_source_tangent_read,sourceTangentPhysicalSpatialJet,
    Complex.ofReal_zero,Pi.div_apply] using generated.comp_ofReal

/-- The original full corrected physical operator has the generated spatial derivative on the source chart. -/
theorem actual_corrected_physical_spatial_derivative (event : DressedEvent) (eps omega : ℝ) (n delta : PhysicalMomentum)
    (eps_ne : eps≠0)
    (regular : sourceTangentRead (sourceTangentThresholdClearing event eps n delta) 0 ((omega/eps^2 : ℝ) : ℂ)≠0) :
    HasDerivAt (fun t : ℝ => correctedPhysicalClock event eps omega (sourceTangentMomentum n delta t))
      (sourceTangentPhysicalSpatialJet event eps omega n delta) 0 := by
  have continuous : Continuous (fun t : ℝ => sourceTangentRead (sourceTangentThresholdClearing event eps n delta)
      t ((omega/eps^2 : ℝ) : ℂ)) := by
    simp only [actual_source_tangent_read]
    fun_prop
  have chart : ∀ᶠt in 𝓝 (0 : ℝ),sourceTangentRead (sourceTangentThresholdClearing event eps n delta)
      t ((omega/eps^2 : ℝ) : ℂ)≠0 := continuous.continuousAt.eventually_ne regular
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have generated := (hasDerivAt_pi.mp (hasDerivAt_pi.mp
    (actual_source_tangent_spatial_derivative event eps omega n delta regular) i)) j
  apply generated.congr_of_eventuallyEq
  filter_upwards [chart] with t ht
  exact congrFun (congrFun (actual_source_tangent_physical_pencil event eps omega t n delta eps_ne ht).symm i) j

end LowEnergy.GaussComposite.ActualDressedEMSourceTransport
