import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraHeavyCurrents0
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraHeavyCurrents1
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraHeavyCurrents2
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraHeavyCurrents3
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraHeavyCurrents4
set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

def heavyIndex79 (i : Fin 31) : Fin 79 := ⟨i.val+48,by omega⟩

theorem actual_heavy_sparse_current (i : Fin 31) (j : Fin 79) :
    sparseCurrentPoint (heavyIndex79 i) j = primalCurrentPoint (heavyIndex79 i) j := by
  fin_cases i
  · exact actual_current_row48 j
  · exact actual_current_row49 j
  · exact actual_current_row50 j
  · exact actual_current_row51 j
  · exact actual_current_row52 j
  · exact actual_current_row53 j
  · exact actual_current_row54 j
  · exact actual_current_row55 j
  · exact actual_current_row56 j
  · exact actual_current_row57 j
  · exact actual_current_row58 j
  · exact actual_current_row59 j
  · exact actual_current_row60 j
  · exact actual_current_row61 j
  · exact actual_current_row62 j
  · exact actual_current_row63 j
  · exact actual_current_row64 j
  · exact actual_current_row65 j
  · exact actual_current_row66 j
  · exact actual_current_row67 j
  · exact actual_current_row68 j
  · exact actual_current_row69 j
  · exact actual_current_row70 j
  · exact actual_current_row71 j
  · exact actual_current_row72 j
  · exact actual_current_row73 j
  · exact actual_current_row74 j
  · exact actual_current_row75 j
  · exact actual_current_row76 j
  · exact actual_current_row77 j
  · exact actual_current_row78 j

end LowEnergy.ActualCanonical79Imaginary
