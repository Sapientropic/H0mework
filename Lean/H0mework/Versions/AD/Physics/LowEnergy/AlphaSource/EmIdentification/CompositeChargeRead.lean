import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeCharge
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeVertexCore

/-! Native time-current charge increments on the actual normalized core
letters and their source-generated local current. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite
open GaussCoreHilbert GaussCoreDifferential
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped InnerProductSpace

theorem creation_vertex_native_test (channel spin : Fin 2) (f : QuantumTest) :
    creationVertexTest .temporal nativeY channel spin f = -creationTest channel spin f := by
  apply DFunLike.ext
  intro z
  change (rootVolume z : ℂ)⁻¹ • creationVertexMatrix .temporal nativeY channel spin z (f z) =
    -((rootVolume z : ℂ)⁻¹ • fiberCreation channel spin (GaussNativePotential.scalarField z) (f z))
  rw [creation_vertex_native_charge,neg_apply,smul_neg]

theorem annihilation_vertex_native_test (channel spin : Fin 2) (f : QuantumTest) :
    annihilationVertexTest .temporal nativeY channel spin f = annihilationTest channel spin f := by
  apply DFunLike.ext
  intro z
  change (rootVolume z : ℂ) • annihilationVertexMatrix .temporal nativeY channel spin z (f z) =
    (rootVolume z : ℂ) • fiberAnnihilation channel spin (GaussNativePotential.scalarField z) (f z)
  rw [annihilation_vertex_native_charge]

theorem creation_charge_core (channel spin : Fin 2) (f : QuantumTest) :
    CanonicalGradedLocalCurrent.sourceAction .temporal nativeY (creationTest channel spin f) -
      creationTest channel spin (CanonicalGradedLocalCurrent.sourceAction .temporal nativeY f) =
        -creationTest channel spin f :=
  (creation_vertex_core .temporal nativeY channel spin f).trans (creation_vertex_native_test channel spin f)

theorem annihilation_charge_core (channel spin : Fin 2) (f : QuantumTest) :
    CanonicalGradedLocalCurrent.sourceAction .temporal nativeY (annihilationTest channel spin f) -
      annihilationTest channel spin (CanonicalGradedLocalCurrent.sourceAction .temporal nativeY f) =
        annihilationTest channel spin f :=
  (annihilation_vertex_core .temporal nativeY channel spin f).trans (annihilation_vertex_native_test channel spin f)

theorem local_current_creation_charge (channel spin : Fin 2) (f : QuantumTest) :
    CanonicalGradedLocalCurrent.localReader (CanonicalGradedLocalCurrent.coreLocalizer f) .temporal nativeY
      (creationSource channel spin f) =
    creationSource channel spin (CanonicalGradedLocalCurrent.sourceAction .temporal nativeY f) -
      creationSource channel spin f := by
  rw [local_current_creation_vertex,creation_vertex_native_test,map_neg,embed_creation_test,sub_eq_add_neg]

theorem local_current_annihilation_charge (channel spin : Fin 2) (f : QuantumTest) :
    CanonicalGradedLocalCurrent.localReader (CanonicalGradedLocalCurrent.coreLocalizer f) .temporal nativeY
      (annihilationSource channel spin f) =
    annihilationSource channel spin (CanonicalGradedLocalCurrent.sourceAction .temporal nativeY f) +
      annihilationSource channel spin f := by
  rw [local_current_annihilation_vertex,annihilation_vertex_native_test,embed_annihilation_test]

theorem creation_charge_vertex_pair (a s b t : Fin 2) (f g : QuantumTest) :
    inner ℂ (creationSource a s f)
      (CanonicalGradedLocalCurrent.localReader (CanonicalGradedLocalCurrent.coreLocalizer g) .temporal nativeY
        (creationSource b t g) -
      creationSource b t (CanonicalGradedLocalCurrent.sourceAction .temporal nativeY g)) =
    -inner ℂ (creationSource a s f) (creationSource b t g) := by
  rw [local_current_creation_charge]
  have h : creationSource b t (CanonicalGradedLocalCurrent.sourceAction .temporal nativeY g) -
      creationSource b t g -
      creationSource b t (CanonicalGradedLocalCurrent.sourceAction .temporal nativeY g) = -creationSource b t g := by abel
  rw [h,inner_neg_right]

end LowEnergy.GaussComposite
