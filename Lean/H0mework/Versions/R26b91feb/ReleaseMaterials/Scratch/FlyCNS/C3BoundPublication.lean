import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3BoundKernel
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3PublishedKernel

set_option autoImplicit false
namespace FlyCNS.C3BoundPublication

/-- The source-sealed installation fixes every numerical law and material.
The complete original Current supplies the current bytes; the kernel
generates its own numerical successor, metadata and pure compressed PL. -/
def generate (installed : FlyCNS.C3BoundKernel.Installation)
    (before : FlyCNS.C3BoundState.RawCurrent) : Except String FlyCNS.C3Published.Result := do
  let state ← FlyCNS.C3BoundState.decode before
  FlyCNS.C3Published.successor installed.kernel state

end FlyCNS.C3BoundPublication
