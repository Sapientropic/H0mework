import H0mework.Versions.R2.Probability.Empirical.Retained
import H0mework.Realization.HilbertTransfer.Chain

/-! The original runtime specializes the shared complete retained-history fold. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedEmpiricalHilbert

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

abbrev stagePullback (depth : Nat) :
    Space read (runtime.advance (depth + 1)) bound →ₗᵢ[ℂ] Space read (runtime.advance depth) bound :=
  pullback read (runtime.advance depth) bound

abbrev Inventory (depth : Nat) :=
  IsometricRetainedTransfer.Chain.Inventory
    (H := fun index => Space read (runtime.advance index) bound)
    (stagePullback read runtime bound) depth

instance inventoryAddCommGroup (depth : Nat) : AddCommGroup (Inventory read runtime bound depth) :=
  IsometricRetainedTransfer.Chain.inventoryAddCommGroup
    (H := fun index => Space read (runtime.advance index) bound)
    (stagePullback read runtime bound) depth

instance inventoryModule (depth : Nat) : Module ℂ (Inventory read runtime bound depth) :=
  IsometricRetainedTransfer.Chain.inventoryModule
    (H := fun index => Space read (runtime.advance index) bound)
    (stagePullback read runtime bound) depth

abbrev retainedHistory (depth : Nat) : Space read runtime bound ≃ₗ[ℂ]
    Space read (runtime.advance depth) bound × Inventory read runtime bound depth :=
  IsometricRetainedTransfer.Chain.retainedHistory
    (H := fun index => Space read (runtime.advance index) bound)
    (stagePullback read runtime bound) depth

abbrev inventoryEnergy (depth : Nat) : Inventory read runtime bound depth → ℝ :=
  IsometricRetainedTransfer.Chain.inventoryEnergy
    (H := fun index => Space read (runtime.advance index) bound)
    (stagePullback read runtime bound) depth

theorem retainedHistory_energy (depth : Nat) (value : Space read runtime bound) :
    ‖value‖ ^ 2 = ‖(retainedHistory read runtime bound depth value).1‖ ^ 2 +
      inventoryEnergy read runtime bound depth (retainedHistory read runtime bound depth value).2 :=
  IsometricRetainedTransfer.Chain.retainedHistory_energy
    (H := fun index => Space read (runtime.advance index) bound)
    (stagePullback read runtime bound) depth value

end
end SourceGeneratedEmpiricalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
