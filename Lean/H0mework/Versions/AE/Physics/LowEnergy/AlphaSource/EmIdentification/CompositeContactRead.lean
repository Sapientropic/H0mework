import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeContact

/-! The actual field contact returns the original weighted source pairing,
including both charged spectral branches and all scalar-coordinate dependence. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace LowEnergy.GaussComposite
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoreHilbert GaussCoreDifferential GaussHalfDensity GaussHistoryHilbert GaussFockLift
open MeasureTheory Filter
open scoped InnerProductSpace ContDiff BigOperators

theorem source_contact (a s b t : Fin 2) (f g : QuantumTest) :
    inner ℂ (creationSource a s f) (creationSource b t g) +
      inner ℂ (annihilationSource b t f) (annihilationSource a s g) =
    GaussFockPair.sourcePair f (contactSource a s b t g) := by
  let U := fockHalfDensityEquiv
  rw [←U.inner_map_map (creationSource a s f) (creationSource b t g),
    ←U.inner_map_map (annihilationSource b t f) (annihilationSource a s g),
    GaussFockPair.sourcePair,←U.inner_map_map (embed f) (embed (contactSource a s b t g)),
    flat_inner_integral,flat_inner_integral,flat_inner_integral]
  rw [←integral_add
    (flat_value_inner_integrable (U (creationSource a s f)) (U (creationSource b t g)))
    (flat_value_inner_integrable (U (annihilationSource b t f)) (U (annihilationSource a s g)))]
  apply integral_congr_ae
  filter_upwards [creation_source_value a s f,creation_source_value b t g,
    annihilation_source_value b t f,annihilation_source_value a s g,
    flat_embed_value f,flat_embed_value (contactSource a s b t g)] with z hc hd ha hb hf hg
  change inner ℂ (flatValue (fockHalfDensityEquiv (creationSource a s f)) z)
      (flatValue (fockHalfDensityEquiv (creationSource b t g)) z) +
    inner ℂ (flatValue (fockHalfDensityEquiv (annihilationSource b t f)) z)
      (flatValue (fockHalfDensityEquiv (annihilationSource a s g)) z) = _
  rw [hc,hd,ha,hb]
  change _ = inner ℂ (flatValue (fockHalfDensityEquiv (embed f)) z)
    (flatValue (fockHalfDensityEquiv (embed (contactSource a s b t g))) z)
  rw [hf,hg,fiber_contact_pair]
  change _ = inner ℂ (weightedValue f z)
    (weightedValue (scalarMultiplier (contactCoefficient a s b t) (contact_coefficient_smooth a s b t) g) z)
  rw [weighted_scalar_value,inner_smul_right]

theorem source_contact_norm (channel spin : Fin 2) (f : QuantumTest) :
    ‖creationSource channel spin f‖^2 + ‖annihilationSource channel spin f‖^2 =
      (GaussFockPair.sourcePair f (contactSource channel spin channel spin f)).re := by
  change _ = RCLike.re (GaussFockPair.sourcePair f (contactSource channel spin channel spin f))
  rw [←source_contact]
  simp only [map_add,inner_self_eq_norm_sq]

theorem source_contact_nonnegative (channel spin : Fin 2) (f : QuantumTest) :
    0 ≤ (GaussFockPair.sourcePair f (contactSource channel spin channel spin f)).re := by
  rw [←source_contact_norm]
  positivity

theorem source_contact_zero_iff (channel spin : Fin 2) (f : QuantumTest) :
    (GaussFockPair.sourcePair f (contactSource channel spin channel spin f)).re = 0 ↔
      creationSource channel spin f=0 ∧ annihilationSource channel spin f=0 := by
  rw [←source_contact_norm]
  constructor
  · intro h
    have hc : ‖creationSource channel spin f‖=0 := by nlinarith [sq_nonneg ‖annihilationSource channel spin f‖]
    have ha : ‖annihilationSource channel spin f‖=0 := by nlinarith [sq_nonneg ‖creationSource channel spin f‖]
    exact ⟨norm_eq_zero.mp hc,norm_eq_zero.mp ha⟩
  · rintro ⟨hc,ha⟩
    simp only [hc,ha,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,add_zero]

theorem source_contact_hermitian (a s b t : Fin 2) (f g : QuantumTest) :
    (starRingEnd ℂ) (GaussFockPair.sourcePair f (contactSource a s b t g)) =
      GaussFockPair.sourcePair g (contactSource b t a s f) := by
  rw [←source_contact,←source_contact,map_add,inner_conj_symm,inner_conj_symm]

end LowEnergy.GaussComposite
