import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3SincosROM
set_option autoImplicit false
namespace FlyCNS.C3CPG
open FlyCNS.C3Actuation
structure Material where
  timestep : Float
  weights : Array Float
  biases : Array Float
  convergence : Array Float
structure State where
  phases : Array Float
  magnitudes : Array Float
  frequencies : Array Float
  amplitudes : Array Float

/-- Original six-oscillator NumPy recurrence; no coupling sine is supplied. -/
def advance (m : Material) (s : State) : State := Id.run do
  let n := s.phases.size
  let twoPi := (Float.ofBits 0x4000000000000000)*(Float.ofBits 0x400921FB54442D18)
  let mut phases := s.phases
  let mut magnitudes := s.magnitudes
  for i in [:n] do
    let mut coupling := Float.ofBits 0x8000000000000000
    for j in [:n] do
      let phase := (s.phases[j]!-s.phases[i]!)-m.biases[i*n+j]!
      let value := (s.magnitudes[j]!*m.weights[i*n+j]!)*FlyCNS.C3Sincos.sine phase
      coupling := coupling+value
    let derivative := twoPi*s.frequencies[i]!+coupling
    phases := phases.set! i (s.phases[i]!+derivative*m.timestep)
    let change := m.convergence[i]!*(s.amplitudes[i]!-s.magnitudes[i]!)
    magnitudes := magnitudes.set! i (s.magnitudes[i]!+change*m.timestep)
  return {s with phases:=phases,magnitudes:=magnitudes}
end FlyCNS.C3CPG
