import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexValuesGauge
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexValuesLorentz
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexValuesCoframe

set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualCandidateVertexValues
open SaturationMonoid.PhysicsCore
open ActualCandidateVertexEntries ActualCandidateVertexLiterals
open DiracCliffordRepresentation
open scoped BigOperators

/-- The nine original scalar-orbit vertices have no degree-two return entry. -/
theorem actual_scalar_values (a : Fin 9) (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false ⟨a.val,by omega⟩ (s,c) (t,d) =
      primalLiteral ⟨a.val,by omega⟩ s t c d := by
  fin_cases a <;>
    change (∑ r : Fin 4, diracGammaZero s r * (0 : ℂ)) = 0 <;> simp


theorem actual_primal_values (a : Fin 97) (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false a (s,c) (t,d) = primalLiteral a s t c d := by
  by_cases h9 : a.val < 9
  · exact actual_scalar_values ⟨a.val,h9⟩ s t c d
  · by_cases h57 : a.val < 57
    · let b : Fin 48 := ⟨a.val-9,by omega⟩
      have he : (⟨b.val+9,by omega⟩ : Fin 97) = a := by
        apply Fin.ext
        dsimp [b]
        omega
      simpa only [he] using actual_gauge_values b s t c d
    · by_cases h73 : a.val < 73
      · let b : Fin 16 := ⟨a.val-57,by omega⟩
        have he : (⟨b.val+57,by omega⟩ : Fin 97) = a := by
          apply Fin.ext
          dsimp [b]
          omega
        simpa only [he] using actual_coframe_values b s t c d
      · let b : Fin 24 := ⟨a.val-73,by omega⟩
        have he : (⟨b.val+73,by omega⟩ : Fin 97) = a := by
          apply Fin.ext
          dsimp [b]
          omega
        simpa only [he] using actual_lorentz_values b s t c d

theorem actual_primitive_literals (dual : Bool) (a : Fin 97)
    (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 dual a (s,c) (t,d) = literalVertex dual a s t c d := by
  cases dual
  · exact actual_primal_values a s t c d
  · change -star (primitiveEntry 0 false a (s,c) (t,d)) = -star (primalLiteral a s t c d)
    rw [actual_primal_values]

/-- All 97 actual zero-leg currents on the same twelve candidate modes,
including the independent negative-conjugate branch and every zero entry. -/
theorem actual_source_literals (dual : Bool) (a : Fin 97)
    (s t : Fin 4) (c d : Fin 3) :
    MixedSpectatorContactVertices.sourceVertex (0 : Fin 4 → ℂ) a
      (supportMode dual (s,c)) (supportMode dual (t,d)) =
      ActualCandidateVertexLiterals.literalVertex dual a s t c d := by
  rw [actual_primitive_entry,actual_primitive_literals]

end LowEnergy.ActualCandidateVertexValues
