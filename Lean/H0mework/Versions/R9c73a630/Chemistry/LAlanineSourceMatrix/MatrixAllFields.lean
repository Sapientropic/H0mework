import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousMatrix.SourceField
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceMatrix.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousSource.RK4Readout
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField02.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField03.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField04.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField05.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField06.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField07.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField08.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField09.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField10.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField11.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField12.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField13.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField14.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField15.MatrixProducer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField16.MatrixProducer

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices

/-- Each registered field is recovered from its own source AO row and the same complete D3. -/
theorem all_actual_fields : SourceRK4Replay.SourceFieldLaw := by
  intro field x inside
  fin_cases field
  · exact SourceSignedMatrix.actual_first_field x inside
  · exact SourceField1Matrix.actual_field x inside
  · exact F2.actual_field x inside
  · exact F3.actual_field x inside
  · exact F4.actual_field x inside
  · exact F5.actual_field x inside
  · exact F6.actual_field x inside
  · exact F7.actual_field x inside
  · exact F8.actual_field x inside
  · exact F9.actual_field x inside
  · exact F10.actual_field x inside
  · exact F11.actual_field x inside
  · exact F12.actual_field x inside
  · exact F13.actual_field x inside
  · exact F14.actual_field x inside
  · exact F15.actual_field x inside
  · exact F16.actual_field x inside

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices
