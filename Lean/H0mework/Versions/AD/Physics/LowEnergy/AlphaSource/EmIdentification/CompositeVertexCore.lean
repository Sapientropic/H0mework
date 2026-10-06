import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeVertex

/-! The generated matrix vertices enter the same source core and actual
bounded local current. The localizer is generated from the input support. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussCoreDifferential GaussFockLift
open CanonicalGradedCurrent
open GaussHistoryHilbert (physicalChart)
open Set Function
open scoped InnerProductSpace ContDiff Distributions

def creationVertexTest (mu : Component) (a : NativeLie) (channel spin : Fin 2) :
    QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z => (rootVolume z : ℂ)⁻¹ • creationVertexMatrix mu a channel spin z)
    (fun z => ((root_volume_complex_smooth z).inv
      (Complex.ofReal_ne_zero.mpr (root_volume_pos z).ne')).smul
        (creation_vertex_smooth mu a channel spin z))

def annihilationVertexTest (mu : Component) (a : NativeLie) (channel spin : Fin 2) :
    QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z => (rootVolume z : ℂ) • annihilationVertexMatrix mu a channel spin z)
    (fun z => (root_volume_complex_smooth z).smul (annihilation_vertex_smooth mu a channel spin z))

theorem creation_vertex_core (mu : Component) (a : NativeLie) (channel spin : Fin 2) (f : QuantumTest) :
    CanonicalGradedLocalCurrent.sourceAction mu a (creationTest channel spin f) -
      creationTest channel spin (CanonicalGradedLocalCurrent.sourceAction mu a f) =
        creationVertexTest mu a channel spin f := by
  apply DFunLike.ext
  intro z
  change CanonicalGradedLocalCurrent.sourceCurrent mu a z
      ((rootVolume z : ℂ)⁻¹ • fiberCreation channel spin (GaussNativePotential.scalarField z) (f z)) -
    (rootVolume z : ℂ)⁻¹ • fiberCreation channel spin (GaussNativePotential.scalarField z)
      (CanonicalGradedLocalCurrent.sourceCurrent mu a z (f z)) =
    (rootVolume z : ℂ)⁻¹ • creationVertexMatrix mu a channel spin z (f z)
  rw [map_smul,←smul_sub]
  exact congrArg (fun v : FockFiber => (rootVolume z : ℂ)⁻¹ • v)
    (congrArg (fun A : FiberOp => A (f z)) (creation_vertex_matrix mu a channel spin z))

theorem annihilation_vertex_core (mu : Component) (a : NativeLie) (channel spin : Fin 2) (f : QuantumTest) :
    CanonicalGradedLocalCurrent.sourceAction mu a (annihilationTest channel spin f) -
      annihilationTest channel spin (CanonicalGradedLocalCurrent.sourceAction mu a f) =
        annihilationVertexTest mu a channel spin f := by
  apply DFunLike.ext
  intro z
  change CanonicalGradedLocalCurrent.sourceCurrent mu a z
      ((rootVolume z : ℂ) • fiberAnnihilation channel spin (GaussNativePotential.scalarField z) (f z)) -
    (rootVolume z : ℂ) • fiberAnnihilation channel spin (GaussNativePotential.scalarField z)
      (CanonicalGradedLocalCurrent.sourceCurrent mu a z (f z)) =
    (rootVolume z : ℂ) • annihilationVertexMatrix mu a channel spin z (f z)
  rw [map_smul,←smul_sub]
  exact congrArg (fun v : FockFiber => (rootVolume z : ℂ) • v)
    (congrArg (fun A : FiberOp => A (f z)) (annihilation_vertex_matrix mu a channel spin z))

theorem creation_test_support (channel spin : Fin 2) (f : QuantumTest) :
    tsupport (creationTest channel spin f) ⊆ tsupport f := multiplier_support _ f

theorem annihilation_test_support (channel spin : Fin 2) (f : QuantumTest) :
    tsupport (annihilationTest channel spin f) ⊆ tsupport f := multiplier_support _ f

theorem local_current_creation_vertex (mu : Component) (a : NativeLie) (channel spin : Fin 2)
    (f : QuantumTest) :
    CanonicalGradedLocalCurrent.localReader (CanonicalGradedLocalCurrent.coreLocalizer f) mu a
      (creationSource channel spin f) =
    creationSource channel spin (CanonicalGradedLocalCurrent.sourceAction mu a f) +
      embed (creationVertexTest mu a channel spin f) := by
  rw [←embed_creation_test,CanonicalGradedLocalCurrent.localReader_core]
  rw [CanonicalGradedLocalCurrent.localAction_exact _ _ _ _ (fun z hz =>
    CanonicalGradedLocalCurrent.coreLocalizer_one f z (creation_test_support channel spin f hz))]
  have h := congrArg embed (creation_vertex_core mu a channel spin f)
  rw [map_sub,embed_creation_test] at h
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

theorem local_current_annihilation_vertex (mu : Component) (a : NativeLie) (channel spin : Fin 2)
    (f : QuantumTest) :
    CanonicalGradedLocalCurrent.localReader (CanonicalGradedLocalCurrent.coreLocalizer f) mu a
      (annihilationSource channel spin f) =
    annihilationSource channel spin (CanonicalGradedLocalCurrent.sourceAction mu a f) +
      embed (annihilationVertexTest mu a channel spin f) := by
  rw [←embed_annihilation_test,CanonicalGradedLocalCurrent.localReader_core]
  rw [CanonicalGradedLocalCurrent.localAction_exact _ _ _ _ (fun z hz =>
    CanonicalGradedLocalCurrent.coreLocalizer_one f z (annihilation_test_support channel spin f hz))]
  have h := congrArg embed (annihilation_vertex_core mu a channel spin f)
  rw [map_sub,embed_annihilation_test] at h
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

end LowEnergy.GaussComposite
