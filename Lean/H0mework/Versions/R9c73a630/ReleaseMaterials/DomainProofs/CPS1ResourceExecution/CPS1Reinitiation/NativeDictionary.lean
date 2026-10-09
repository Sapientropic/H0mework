import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Reinitiation.Source

set_option autoImplicit false
namespace CPS1Reinitiation.NativeDictionary
open CPS1ResourceExecution

def embedded (frame : CPS1Recycling.Frame) (species : CPS1ResourceExecution.Species) : Species frame :=
  .retained (.old species)

def nativeReactants (frame : CPS1Recycling.Frame) (reaction : Reaction) : Stock frame :=
  reaction.reactants.map (embedded frame)

def nativeProducts (frame : CPS1Recycling.Frame) (reaction : Reaction) : Stock frame :=
  reaction.products.map (embedded frame)

end CPS1Reinitiation.NativeDictionary
