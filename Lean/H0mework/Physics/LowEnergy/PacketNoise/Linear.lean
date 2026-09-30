import H0mework.Physics.LowEnergy.PacketNoise.Graph

set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace SpatialGreen
noncomputable section

theorem equation_add (energy damping : ℝ) (first second firstLoad secondLoad : FullMatterL2)
    (firstEquation : Equation 0 energy damping first firstLoad)
    (secondEquation : Equation 0 energy damping second secondLoad) :
    Equation 0 energy damping (first+second) (firstLoad+secondLoad) := by
  filter_upwards [firstEquation,secondEquation,Lp.coeFn_add (fourier first) (fourier second),
    Lp.coeFn_add (fourier firstLoad) (fourier secondLoad)] with frequency f g inputs outputs
  change symbol 0 energy damping frequency (fourier first frequency)=fourier firstLoad frequency at f
  change symbol 0 energy damping frequency (fourier second frequency)=fourier secondLoad frequency at g
  change symbol 0 energy damping frequency (fourier (first+second) frequency)=fourier (firstLoad+secondLoad) frequency
  rw [map_add,map_add,inputs,outputs]
  simp only [Pi.add_apply,map_add,f,g]

theorem equation_smul (energy damping : ℝ) (field load : FullMatterL2) (scale : ℂ)
    (equation : Equation 0 energy damping field load) :
    Equation 0 energy damping (scale • field) (scale • load) := by
  filter_upwards [equation,Lp.coeFn_smul scale (fourier field),Lp.coeFn_smul scale (fourier load)]
    with frequency original input output
  change symbol 0 energy damping frequency (fourier field frequency)=fourier load frequency at original
  change symbol 0 energy damping frequency (fourier (scale • field) frequency)=fourier (scale • load) frequency
  rw [map_smul,map_smul,input,output]
  simp only [Pi.smul_apply,map_smul,original]

def SourceMap.add {energy damping : ℝ} (first second : SourceMap energy damping) : SourceMap energy damping where
  field := first.field+second.field
  load := first.load+second.load
  equation input := equation_add energy damping _ _ _ _ (first.equation input) (second.equation input)

def SourceMap.scale {energy damping : ℝ} (map : SourceMap energy damping) (scalar : ℂ) : SourceMap energy damping where
  field := scalar • map.field
  load := scalar • map.load
  equation input := equation_smul energy damping _ _ scalar (map.equation input)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
