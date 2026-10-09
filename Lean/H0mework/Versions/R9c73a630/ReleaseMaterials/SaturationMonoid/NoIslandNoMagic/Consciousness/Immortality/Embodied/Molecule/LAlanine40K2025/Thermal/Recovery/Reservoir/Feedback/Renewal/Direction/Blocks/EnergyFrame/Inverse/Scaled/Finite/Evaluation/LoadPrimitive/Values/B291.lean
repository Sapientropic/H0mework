import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B194

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4657_pa : Scalar.QComplex := ((999996860372020337092156463017 : Int)/10^30,(-2505842393699564857946775726 : Int)/10^30)
theorem v4657_pa_checked : Scalar.distance (sourceCoefficient 83 93 1 0) v4657_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4657_pb : Scalar.QComplex := ((-1081214651066330772455286 : Int)/10^30,(-431476161139682141118694708 : Int)/10^30)
theorem v4657_pb_checked : Scalar.distance (sourceCoefficient 83 93 1 1) v4657_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4657_pg : Scalar.QComplex := ((-93086137081229194016955 : Int)/10^30,(233259920913247422370 : Int)/10^30)
theorem v4657_pg_checked : Scalar.distance (sourceCoefficient 83 93 1 2) v4657_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4657_mb : Scalar.QComplex := ((-1453558742579335752873504 : Int)/10^30,(-431475067441840144047470568 : Int)/10^30)
theorem v4657_mb_checked : Scalar.distance (sourceCoefficient 83 93 3 1) v4657_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4657_mg : Scalar.QComplex := ((-93085901128200000764503 : Int)/10^30,(313588977917035853367 : Int)/10^30)
theorem v4657_mg_checked : Scalar.distance (sourceCoefficient 83 93 3 2) v4657_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4657_upper : Scalar.QComplex := ((999991046137521416572549690946 : Int)/10^30,(-4231742523537268508475681565 : Int)/10^30)
theorem v4657_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 83 93 5) 1) 14) v4657_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4657 : Material (83 : Basis) (93 : Basis) where
  plus := ![v4657_pa,v4657_pb,v4657_pg]
  minus := ![(Primitive.Addresses.material4657 1).one,v4657_mb,v4657_mg]
  upper := v4657_upper
  lower := (Primitive.Addresses.material4657 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4657_pa_checked.trans (by decide +kernel)
    · exact v4657_pb_checked.trans (by decide +kernel)
    · exact v4657_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 83 93 Primitive.Addresses.material4657
    · exact v4657_mb_checked.trans (by decide +kernel)
    · exact v4657_mg_checked.trans (by decide +kernel)
  upper_error := v4657_upper_checked
  lower_error := reuse_lower_error 83 93 Primitive.Addresses.material4657

def v4658_pa : Scalar.QComplex := ((999996747110443596247894986769 : Int)/10^30,(-2550640808016102852500714517 : Int)/10^30)
theorem v4658_pa_checked : Scalar.distance (sourceCoefficient 83 94 1 0) v4658_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4658_pb : Scalar.QComplex := ((-1100544154808494116573234 : Int)/10^30,(-431476110395924702332777412 : Int)/10^30)
theorem v4658_pb_checked : Scalar.distance (sourceCoefficient 83 94 1 1) v4658_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4658_pg : Scalar.QComplex := ((-93086126335973362421540 : Int)/10^30,(237430044826389320992 : Int)/10^30)
theorem v4658_pg_checked : Scalar.distance (sourceCoefficient 83 94 1 2) v4658_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4658_mb : Scalar.QComplex := ((-1472888195334664196146320 : Int)/10^30,(-431475000017610438526110112 : Int)/10^30)
theorem v4658_mb_checked : Scalar.distance (sourceCoefficient 83 94 3 1) v4658_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4658_mg : Scalar.QComplex := ((-93085886784319048486469 : Int)/10^30,(317759091004778200740 : Int)/10^30)
theorem v4658_mg_checked : Scalar.distance (sourceCoefficient 83 94 3 2) v4658_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4658_upper : Scalar.QComplex := ((999990855558114335597568156985 : Int)/10^30,(-4276540675652624325235493397 : Int)/10^30)
theorem v4658_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 83 94 5) 1) 14) v4658_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4658 : Material (83 : Basis) (94 : Basis) where
  plus := ![v4658_pa,v4658_pb,v4658_pg]
  minus := ![(Primitive.Addresses.material4658 1).one,v4658_mb,v4658_mg]
  upper := v4658_upper
  lower := (Primitive.Addresses.material4658 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4658_pa_checked.trans (by decide +kernel)
    · exact v4658_pb_checked.trans (by decide +kernel)
    · exact v4658_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 83 94 Primitive.Addresses.material4658
    · exact v4658_mb_checked.trans (by decide +kernel)
    · exact v4658_mg_checked.trans (by decide +kernel)
  upper_error := v4658_upper_checked
  lower_error := reuse_lower_error 83 94 Primitive.Addresses.material4658

def v4659_pa : Scalar.QComplex := ((999996633202701734398072421794 : Int)/10^30,(-2594914885156574118533253575 : Int)/10^30)
theorem v4659_pa_checked : Scalar.distance (sourceCoefficient 83 95 1 0) v4659_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4659_pb : Scalar.QComplex := ((-1119647418003545217783072 : Int)/10^30,(-431476059111698104797895935 : Int)/10^30)
theorem v4659_pb_checked : Scalar.distance (sourceCoefficient 83 95 1 1) v4659_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4659_pg : Scalar.QComplex := ((-93086115502342852763511 : Int)/10^30,(241551359972899746633 : Int)/10^30)
theorem v4659_pg_checked : Scalar.distance (sourceCoefficient 83 95 1 2) v4659_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4659_mb : Scalar.QComplex := ((-1491991407160719549731653 : Int)/10^30,(-431474932248147178159029502 : Int)/10^30)
theorem v4659_mb_checked : Scalar.distance (sourceCoefficient 83 95 3 1) v4659_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4659_mg : Scalar.QComplex := ((-93085872394183218389470 : Int)/10^30,(321880395267799442698 : Int)/10^30)
theorem v4659_mg_checked : Scalar.distance (sourceCoefficient 83 95 3 2) v4659_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4659_upper : Scalar.QComplex := ((999990665237501494398206934637 : Int)/10^30,(-4320814490257629665040194248 : Int)/10^30)
theorem v4659_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 83 95 5) 1) 14) v4659_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4659 : Material (83 : Basis) (95 : Basis) where
  plus := ![v4659_pa,v4659_pb,v4659_pg]
  minus := ![(Primitive.Addresses.material4659 1).one,v4659_mb,v4659_mg]
  upper := v4659_upper
  lower := (Primitive.Addresses.material4659 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4659_pa_checked.trans (by decide +kernel)
    · exact v4659_pb_checked.trans (by decide +kernel)
    · exact v4659_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 83 95 Primitive.Addresses.material4659
    · exact v4659_mb_checked.trans (by decide +kernel)
    · exact v4659_mg_checked.trans (by decide +kernel)
  upper_error := v4659_upper_checked
  lower_error := reuse_lower_error 83 95 Primitive.Addresses.material4659

def v4660_pa : Scalar.QComplex := ((999996577798100682895222826960 : Int)/10^30,(-2616178909625327949113074520 : Int)/10^30)
theorem v4660_pa_checked : Scalar.distance (sourceCoefficient 83 96 1 0) v4660_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4660_pb : Scalar.QComplex := ((-1128822363426786119997344 : Int)/10^30,(-431476034079952131341073145 : Int)/10^30)
theorem v4660_pb_checked : Scalar.distance (sourceCoefficient 83 96 1 1) v4660_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4660_pg : Scalar.QComplex := ((-93086110223475547059205 : Int)/10^30,(243530751757116554617 : Int)/10^30)
theorem v4660_pg_checked : Scalar.distance (sourceCoefficient 83 96 1 2) v4660_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4660_mb : Scalar.QComplex := ((-1501166327566439568047675 : Int)/10^30,(-431474899298845849110600663 : Int)/10^30)
theorem v4660_mb_checked : Scalar.distance (sourceCoefficient 83 96 3 1) v4660_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4660_mg : Scalar.QComplex := ((-93085865407191916966226 : Int)/10^30,(323859781759573493280 : Int)/10^30)
theorem v4660_mg_checked : Scalar.distance (sourceCoefficient 83 96 3 2) v4660_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4660_upper : Scalar.QComplex := ((999990573133205785702067572106 : Int)/10^30,(-4342078387432801748439958228 : Int)/10^30)
theorem v4660_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 83 96 5) 1) 14) v4660_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4660 : Material (83 : Basis) (96 : Basis) where
  plus := ![v4660_pa,v4660_pb,v4660_pg]
  minus := ![(Primitive.Addresses.material4660 1).one,v4660_mb,v4660_mg]
  upper := v4660_upper
  lower := (Primitive.Addresses.material4660 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4660_pa_checked.trans (by decide +kernel)
    · exact v4660_pb_checked.trans (by decide +kernel)
    · exact v4660_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 83 96 Primitive.Addresses.material4660
    · exact v4660_mb_checked.trans (by decide +kernel)
    · exact v4660_mg_checked.trans (by decide +kernel)
  upper_error := v4660_upper_checked
  lower_error := reuse_lower_error 83 96 Primitive.Addresses.material4660

def v4661_pa : Scalar.QComplex := ((999996383716288969002652982397 : Int)/10^30,(-2689340875484942318938671834 : Int)/10^30)
theorem v4661_pa_checked : Scalar.distance (sourceCoefficient 83 97 1 0) v4661_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4661_pb : Scalar.QComplex := ((-1160390094578367275973576 : Int)/10^30,(-431475945967366024101313134 : Int)/10^30)
theorem v4661_pb_checked : Scalar.distance (sourceCoefficient 83 97 1 1) v4661_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4661_pg : Scalar.QComplex := ((-93086091685633570519800 : Int)/10^30,(250341136613887934423 : Int)/10^30)
theorem v4661_pg_checked : Scalar.distance (sourceCoefficient 83 97 1 2) v4661_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4661_mb : Scalar.QComplex := ((-1532733970926718332719777 : Int)/10^30,(-431474783944762324231990489 : Int)/10^30)
theorem v4661_mb_checked : Scalar.distance (sourceCoefficient 83 97 3 1) v4661_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4661_mg : Scalar.QComplex := ((-93085840992301439866567 : Int)/10^30,(330670148083204628601 : Int)/10^30)
theorem v4661_mg_checked : Scalar.distance (sourceCoefficient 83 97 3 2) v4661_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4661_upper : Scalar.QComplex := ((999990252780767261871001990296 : Int)/10^30,(-4415239909358662124832072795 : Int)/10^30)
theorem v4661_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 83 97 5) 1) 14) v4661_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4661 : Material (83 : Basis) (97 : Basis) where
  plus := ![v4661_pa,v4661_pb,v4661_pg]
  minus := ![(Primitive.Addresses.material4661 1).one,v4661_mb,v4661_mg]
  upper := v4661_upper
  lower := (Primitive.Addresses.material4661 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4661_pa_checked.trans (by decide +kernel)
    · exact v4661_pb_checked.trans (by decide +kernel)
    · exact v4661_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 83 97 Primitive.Addresses.material4661
    · exact v4661_mb_checked.trans (by decide +kernel)
    · exact v4661_mg_checked.trans (by decide +kernel)
  upper_error := v4661_upper_checked
  lower_error := reuse_lower_error 83 97 Primitive.Addresses.material4661

def v4662_pa : Scalar.QComplex := ((999997151740145509345258217531 : Int)/10^30,(-2386736599710389236155204806 : Int)/10^30)
theorem v4662_pa_checked : Scalar.distance (sourceCoefficient 84 85 1 0) v4662_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4662_pb : Scalar.QComplex := ((-1029823190251836690372731 : Int)/10^30,(-431476291591098427435655162 : Int)/10^30)
theorem v4662_pb_checked : Scalar.distance (sourceCoefficient 84 85 1 1) v4662_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4662_pg : Scalar.QComplex := ((-93086164714152551465154 : Int)/10^30,(222172789055773505079 : Int)/10^30)
theorem v4662_pg_checked : Scalar.distance (sourceCoefficient 84 85 1 2) v4662_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4662_mb : Scalar.QComplex := ((-1402167413473928179218635 : Int)/10^30,(-431475242241723954774982955 : Int)/10^30)
theorem v4662_mb_checked : Scalar.distance (sourceCoefficient 84 85 3 1) v4662_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4662_mg : Scalar.QComplex := ((-93085938328808516330168 : Int)/10^30,(302501874033776150382 : Int)/10^30)
theorem v4662_mg_checked : Scalar.distance (sourceCoefficient 84 85 3 2) v4662_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4662_upper : Scalar.QComplex := ((999991543071007862321674272682 : Int)/10^30,(-4112637409817133221648815751 : Int)/10^30)
theorem v4662_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 84 85 5) 1) 14) v4662_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4662 : Material (84 : Basis) (85 : Basis) where
  plus := ![v4662_pa,v4662_pb,v4662_pg]
  minus := ![(Primitive.Addresses.material4662 1).one,v4662_mb,v4662_mg]
  upper := v4662_upper
  lower := (Primitive.Addresses.material4662 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4662_pa_checked.trans (by decide +kernel)
    · exact v4662_pb_checked.trans (by decide +kernel)
    · exact v4662_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 84 85 Primitive.Addresses.material4662
    · exact v4662_mb_checked.trans (by decide +kernel)
    · exact v4662_mg_checked.trans (by decide +kernel)
  upper_error := v4662_upper_checked
  lower_error := reuse_lower_error 84 85 Primitive.Addresses.material4662

def v4663_pa : Scalar.QComplex := ((999997116824086023083130591909 : Int)/10^30,(-2401321202015774232560577947 : Int)/10^30)
theorem v4663_pa_checked : Scalar.distance (sourceCoefficient 84 86 1 0) v4663_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4663_pb : Scalar.QComplex := ((-1036116117857837801871308 : Int)/10^30,(-431476276344474013334204287 : Int)/10^30)
theorem v4663_pb_checked : Scalar.distance (sourceCoefficient 84 86 1 1) v4663_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4663_pg : Scalar.QComplex := ((-93086161444402886815696 : Int)/10^30,(223530417568223933005 : Int)/10^30)
theorem v4663_pg_checked : Scalar.distance (sourceCoefficient 84 86 1 2) v4663_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4663_mb : Scalar.QComplex := ((-1408460325579634555106834 : Int)/10^30,(-431475221564592116647867657 : Int)/10^30)
theorem v4663_mb_checked : Scalar.distance (sourceCoefficient 84 86 3 1) v4663_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4663_mg : Scalar.QComplex := ((-93085933887487808231606 : Int)/10^30,(303859499219072739900 : Int)/10^30)
theorem v4663_mg_checked : Scalar.distance (sourceCoefficient 84 86 3 2) v4663_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4663_upper : Scalar.QComplex := ((999991482983299905119736313657 : Int)/10^30,(-4127221930138515198802250911 : Int)/10^30)
theorem v4663_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 84 86 5) 1) 14) v4663_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4663 : Material (84 : Basis) (86 : Basis) where
  plus := ![v4663_pa,v4663_pb,v4663_pg]
  minus := ![(Primitive.Addresses.material4663 1).one,v4663_mb,v4663_mg]
  upper := v4663_upper
  lower := (Primitive.Addresses.material4663 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4663_pa_checked.trans (by decide +kernel)
    · exact v4663_pb_checked.trans (by decide +kernel)
    · exact v4663_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 84 86 Primitive.Addresses.material4663
    · exact v4663_mb_checked.trans (by decide +kernel)
    · exact v4663_mg_checked.trans (by decide +kernel)
  upper_error := v4663_upper_checked
  lower_error := reuse_lower_error 84 86 Primitive.Addresses.material4663

def v4664_pa : Scalar.QComplex := ((999997114504528265323391472979 : Int)/10^30,(-2402286955670624253188023273 : Int)/10^30)
theorem v4664_pa_checked : Scalar.distance (sourceCoefficient 84 87 1 0) v4664_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4664_pb : Scalar.QComplex := ((-1036532818818713464373873 : Int)/10^30,(-431476275330563081580017429 : Int)/10^30)
theorem v4664_pb_checked : Scalar.distance (sourceCoefficient 84 87 1 1) v4664_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4664_pg : Scalar.QComplex := ((-93086161227073262595944 : Int)/10^30,(223620316124660294503 : Int)/10^30)
theorem v4664_pg_checked : Scalar.distance (sourceCoefficient 84 87 1 2) v4664_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4664_mb : Scalar.QComplex := ((-1408877025510393936450020 : Int)/10^30,(-431475220191087400697956920 : Int)/10^30)
theorem v4664_mb_checked : Scalar.distance (sourceCoefficient 84 87 3 1) v4664_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4664_mg : Scalar.QComplex := ((-93085933592579859609706 : Int)/10^30,(303949397554490082730 : Int)/10^30)
theorem v4664_mg_checked : Scalar.distance (sourceCoefficient 84 87 3 2) v4664_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4664_upper : Scalar.QComplex := ((999991478996942406284844182712 : Int)/10^30,(-4128187678351642334666689383 : Int)/10^30)
theorem v4664_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 84 87 5) 1) 14) v4664_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4664 : Material (84 : Basis) (87 : Basis) where
  plus := ![v4664_pa,v4664_pb,v4664_pg]
  minus := ![(Primitive.Addresses.material4664 1).one,v4664_mb,v4664_mg]
  upper := v4664_upper
  lower := (Primitive.Addresses.material4664 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4664_pa_checked.trans (by decide +kernel)
    · exact v4664_pb_checked.trans (by decide +kernel)
    · exact v4664_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 84 87 Primitive.Addresses.material4664
    · exact v4664_mb_checked.trans (by decide +kernel)
    · exact v4664_mg_checked.trans (by decide +kernel)
  upper_error := v4664_upper_checked
  lower_error := reuse_lower_error 84 87 Primitive.Addresses.material4664

def v4665_pa : Scalar.QComplex := ((999997086185466242966503368061 : Int)/10^30,(-2414046515127438438055353610 : Int)/10^30)
theorem v4665_pa_checked : Scalar.distance (sourceCoefficient 84 88 1 0) v4665_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4665_pb : Scalar.QComplex := ((-1041606803963346069431692 : Int)/10^30,(-431476262941567867764735345 : Int)/10^30)
theorem v4665_pb_checked : Scalar.distance (sourceCoefficient 84 88 1 1) v4665_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4665_pg : Scalar.QComplex := ((-93086158572619774077755 : Int)/10^30,(224714971486582765088 : Int)/10^30)
theorem v4665_pg_checked : Scalar.distance (sourceCoefficient 84 88 1 2) v4665_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4665_mb : Scalar.QComplex := ((-1413950998074605089692949 : Int)/10^30,(-431475203423476143861571581 : Int)/10^30)
theorem v4665_mb_checked : Scalar.distance (sourceCoefficient 84 88 3 1) v4665_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4665_mg : Scalar.QComplex := ((-93085929993489083574119 : Int)/10^30,(305044050218148525406 : Int)/10^30)
theorem v4665_mg_checked : Scalar.distance (sourceCoefficient 84 88 3 2) v4665_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4665_upper : Scalar.QComplex := ((999991430381989758283354855796 : Int)/10^30,(-4139947171417842118149469079 : Int)/10^30)
theorem v4665_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 84 88 5) 1) 14) v4665_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4665 : Material (84 : Basis) (88 : Basis) where
  plus := ![v4665_pa,v4665_pb,v4665_pg]
  minus := ![(Primitive.Addresses.material4665 1).one,v4665_mb,v4665_mg]
  upper := v4665_upper
  lower := (Primitive.Addresses.material4665 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4665_pa_checked.trans (by decide +kernel)
    · exact v4665_pb_checked.trans (by decide +kernel)
    · exact v4665_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 84 88 Primitive.Addresses.material4665
    · exact v4665_mb_checked.trans (by decide +kernel)
    · exact v4665_mg_checked.trans (by decide +kernel)
  upper_error := v4665_upper_checked
  lower_error := reuse_lower_error 84 88 Primitive.Addresses.material4665

def v4666_pa : Scalar.QComplex := ((999997047215266812070788071855 : Int)/10^30,(-2430135952459898461667316390 : Int)/10^30)
theorem v4666_pa_checked : Scalar.distance (sourceCoefficient 84 89 1 0) v4666_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4666_pb : Scalar.QComplex := ((-1048549033841362950401696 : Int)/10^30,(-431476245862045730910570502 : Int)/10^30)
theorem v4666_pb_checked : Scalar.distance (sourceCoefficient 84 89 1 1) v4666_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4666_pg : Scalar.QComplex := ((-93086154916463852012810 : Int)/10^30,(226212679696097603101 : Int)/10^30)
theorem v4666_pg_checked : Scalar.distance (sourceCoefficient 84 89 1 2) v4666_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4666_mb : Scalar.QComplex := ((-1420893210628854140514736 : Int)/10^30,(-431475180353128648192485266 : Int)/10^30)
theorem v4666_mb_checked : Scalar.distance (sourceCoefficient 84 89 3 1) v4666_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4666_mg : Scalar.QComplex := ((-93085925044879792325549 : Int)/10^30,(306541754714900254779 : Int)/10^30)
theorem v4666_mg_checked : Scalar.distance (sourceCoefficient 84 89 3 2) v4666_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4666_upper : Scalar.QComplex := ((999991363642939155448786602347 : Int)/10^30,(-4156036517527946364286157346 : Int)/10^30)
theorem v4666_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 84 89 5) 1) 14) v4666_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4666 : Material (84 : Basis) (89 : Basis) where
  plus := ![v4666_pa,v4666_pb,v4666_pg]
  minus := ![(Primitive.Addresses.material4666 1).one,v4666_mb,v4666_mg]
  upper := v4666_upper
  lower := (Primitive.Addresses.material4666 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4666_pa_checked.trans (by decide +kernel)
    · exact v4666_pb_checked.trans (by decide +kernel)
    · exact v4666_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 84 89 Primitive.Addresses.material4666
    · exact v4666_mb_checked.trans (by decide +kernel)
    · exact v4666_mg_checked.trans (by decide +kernel)
  upper_error := v4666_upper_checked
  lower_error := reuse_lower_error 84 89 Primitive.Addresses.material4666

def v4667_pa : Scalar.QComplex := ((999996983195260116312555394448 : Int)/10^30,(-2456338815932471540710180222 : Int)/10^30)
theorem v4667_pa_checked : Scalar.distance (sourceCoefficient 84 90 1 0) v4667_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4667_pb : Scalar.QComplex := ((-1059854979132498220193606 : Int)/10^30,(-431476217727982403934660454 : Int)/10^30)
theorem v4667_pb_checked : Scalar.distance (sourceCoefficient 84 90 1 1) v4667_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4667_pg : Scalar.QComplex := ((-93086148901962803598119 : Int)/10^30,(228651810571426963718 : Int)/10^30)
theorem v4667_pg_checked : Scalar.distance (sourceCoefficient 84 90 1 2) v4667_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4667_mb : Scalar.QComplex := ((-1432199127431839731185983 : Int)/10^30,(-431475142462554211437892028 : Int)/10^30)
theorem v4667_mb_checked : Scalar.distance (sourceCoefficient 84 90 3 1) v4667_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4667_mg : Scalar.QComplex := ((-93085916925520892351875 : Int)/10^30,(308980879491786195011 : Int)/10^30)
theorem v4667_mg_checked : Scalar.distance (sourceCoefficient 84 90 3 2) v4667_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4667_upper : Scalar.QComplex := ((999991254399262561514379567536 : Int)/10^30,(-4182239231481708598253233923 : Int)/10^30)
theorem v4667_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 84 90 5) 1) 14) v4667_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4667 : Material (84 : Basis) (90 : Basis) where
  plus := ![v4667_pa,v4667_pb,v4667_pg]
  minus := ![(Primitive.Addresses.material4667 1).one,v4667_mb,v4667_mg]
  upper := v4667_upper
  lower := (Primitive.Addresses.material4667 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4667_pa_checked.trans (by decide +kernel)
    · exact v4667_pb_checked.trans (by decide +kernel)
    · exact v4667_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 84 90 Primitive.Addresses.material4667
    · exact v4667_mb_checked.trans (by decide +kernel)
    · exact v4667_mg_checked.trans (by decide +kernel)
  upper_error := v4667_upper_checked
  lower_error := reuse_lower_error 84 90 Primitive.Addresses.material4667

def v4668_pa : Scalar.QComplex := ((999996946828124205692841239101 : Int)/10^30,(-2471099842120935261704207775 : Int)/10^30)
theorem v4668_pa_checked : Scalar.distance (sourceCoefficient 84 91 1 0) v4668_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4668_pb : Scalar.QComplex := ((-1066224029277647062201119 : Int)/10^30,(-431476201705105725238769312 : Int)/10^30)
theorem v4668_pb_checked : Scalar.distance (sourceCoefficient 84 91 1 1) v4668_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4668_pg : Scalar.QComplex := ((-93086145480941522552859 : Int)/10^30,(230025861710092686362 : Int)/10^30)
theorem v4668_pg_checked : Scalar.distance (sourceCoefficient 84 91 1 2) v4668_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4668_mb : Scalar.QComplex := ((-1438568161378479194045692 : Int)/10^30,(-431475120943480074897933463 : Int)/10^30)
theorem v4668_mb_checked : Scalar.distance (sourceCoefficient 84 91 3 1) v4668_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4668_mg : Scalar.QComplex := ((-93085912318756637406675 : Int)/10^30,(310354927166642593028 : Int)/10^30)
theorem v4668_mg_checked : Scalar.distance (sourceCoefficient 84 91 3 2) v4668_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4668_upper : Scalar.QComplex := ((999991192555988724018503423938 : Int)/10^30,(-4197000172918980382538368895 : Int)/10^30)
theorem v4668_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 84 91 5) 1) 14) v4668_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4668 : Material (84 : Basis) (91 : Basis) where
  plus := ![v4668_pa,v4668_pb,v4668_pg]
  minus := ![(Primitive.Addresses.material4668 1).one,v4668_mb,v4668_mg]
  upper := v4668_upper
  lower := (Primitive.Addresses.material4668 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4668_pa_checked.trans (by decide +kernel)
    · exact v4668_pb_checked.trans (by decide +kernel)
    · exact v4668_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 84 91 Primitive.Addresses.material4668
    · exact v4668_mb_checked.trans (by decide +kernel)
    · exact v4668_mg_checked.trans (by decide +kernel)
  upper_error := v4668_upper_checked
  lower_error := reuse_lower_error 84 91 Primitive.Addresses.material4668

def v4669_pa : Scalar.QComplex := ((999996867350804338528554791031 : Int)/10^30,(-2503055847925083714701902132 : Int)/10^30)
theorem v4669_pa_checked : Scalar.distance (sourceCoefficient 84 92 1 0) v4669_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4669_pb : Scalar.QComplex := ((-1080012325317873543352819 : Int)/10^30,(-431476166587896253538270633 : Int)/10^30)
theorem v4669_pb_checked : Scalar.distance (sourceCoefficient 84 92 1 1) v4669_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4669_pg : Scalar.QComplex := ((-93086137993739743040916 : Int)/10^30,(233000531974920663468 : Int)/10^30)
theorem v4669_pg_checked : Scalar.distance (sourceCoefficient 84 92 1 2) v4669_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4669_mb : Scalar.QComplex := ((-1452356421980122749486250 : Int)/10^30,(-431475073927605198024984970 : Int)/10^30)
theorem v4669_mb_checked : Scalar.distance (sourceCoefficient 84 92 3 1) v4669_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4669_mg : Scalar.QComplex := ((-93085902264551181350965 : Int)/10^30,(313329589862746956723 : Int)/10^30)
theorem v4669_mg_checked : Scalar.distance (sourceCoefficient 84 92 3 2) v4669_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4669_upper : Scalar.QComplex := ((999991057925620237226469870730 : Int)/10^30,(-4228955993957768041800275264 : Int)/10^30)
theorem v4669_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 84 92 5) 1) 14) v4669_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4669 : Material (84 : Basis) (92 : Basis) where
  plus := ![v4669_pa,v4669_pb,v4669_pg]
  minus := ![(Primitive.Addresses.material4669 1).one,v4669_mb,v4669_mg]
  upper := v4669_upper
  lower := (Primitive.Addresses.material4669 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4669_pa_checked.trans (by decide +kernel)
    · exact v4669_pb_checked.trans (by decide +kernel)
    · exact v4669_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 84 92 Primitive.Addresses.material4669
    · exact v4669_mb_checked.trans (by decide +kernel)
    · exact v4669_mg_checked.trans (by decide +kernel)
  upper_error := v4669_upper_checked
  lower_error := reuse_lower_error 84 92 Primitive.Addresses.material4669

def v4670_pa : Scalar.QComplex := ((999996771701706451081814939666 : Int)/10^30,(-2540981339008211653825032488 : Int)/10^30)
theorem v4670_pa_checked : Scalar.distance (sourceCoefficient 84 93 1 0) v4670_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4670_pb : Scalar.QComplex := ((-1096376319118251669438651 : Int)/10^30,(-431476124148312149401955663 : Int)/10^30)
theorem v4670_pb_checked : Scalar.distance (sourceCoefficient 84 93 1 1) v4670_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4670_pg : Scalar.QComplex := ((-93086128963991372956305 : Int)/10^30,(236530880210250827082 : Int)/10^30)
theorem v4670_pg_checked : Scalar.distance (sourceCoefficient 84 93 1 2) v4670_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4670_mb : Scalar.QComplex := ((-1468720373063988438272642 : Int)/10^30,(-431475017366647253280880043 : Int)/10^30)
theorem v4670_mb_checked : Scalar.distance (sourceCoefficient 84 93 3 1) v4670_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4670_mg : Scalar.QComplex := ((-93085890188274647346546 : Int)/10^30,(316859928991300968826 : Int)/10^30)
theorem v4670_mg_checked : Scalar.distance (sourceCoefficient 84 93 3 2) v4670_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4670_upper : Scalar.QComplex := ((999990896820707772071252886424 : Int)/10^30,(-4266881263473666318381101332 : Int)/10^30)
theorem v4670_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 84 93 5) 1) 14) v4670_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4670 : Material (84 : Basis) (93 : Basis) where
  plus := ![v4670_pa,v4670_pb,v4670_pg]
  minus := ![(Primitive.Addresses.material4670 1).one,v4670_mb,v4670_mg]
  upper := v4670_upper
  lower := (Primitive.Addresses.material4670 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4670_pa_checked.trans (by decide +kernel)
    · exact v4670_pb_checked.trans (by decide +kernel)
    · exact v4670_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 84 93 Primitive.Addresses.material4670
    · exact v4670_mb_checked.trans (by decide +kernel)
    · exact v4670_mg_checked.trans (by decide +kernel)
  upper_error := v4670_upper_checked
  lower_error := reuse_lower_error 84 93 Primitive.Addresses.material4670

def v4671_pa : Scalar.QComplex := ((999996656865955737953486941887 : Int)/10^30,(-2585779749317187131220827944 : Int)/10^30)
theorem v4671_pa_checked : Scalar.distance (sourceCoefficient 84 94 1 0) v4671_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4671_pb : Scalar.QComplex := ((-1115705821707632935912827 : Int)/10^30,(-431476072951740928029881048 : Int)/10^30)
theorem v4671_pb_checked : Scalar.distance (sourceCoefficient 84 94 1 1) v4671_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4671_pg : Scalar.QComplex := ((-93086118096623679388564 : Int)/10^30,(240701003812517987870 : Int)/10^30)
theorem v4671_pg_checked : Scalar.distance (sourceCoefficient 84 94 1 2) v4671_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4671_mb : Scalar.QComplex := ((-1488049824275777332738993 : Int)/10^30,(-431474949489604928575641765 : Int)/10^30)
theorem v4671_mb_checked : Scalar.distance (sourceCoefficient 84 94 3 1) v4671_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4671_mg : Scalar.QComplex := ((-93085875722282146834912 : Int)/10^30,(321030041662791656948 : Int)/10^30)
theorem v4671_mg_checked : Scalar.distance (sourceCoefficient 84 94 3 2) v4671_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4671_upper : Scalar.QComplex := ((999990704667135980048762467060 : Int)/10^30,(-4311679408864584118561290104 : Int)/10^30)
theorem v4671_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 84 94 5) 1) 14) v4671_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4671 : Material (84 : Basis) (94 : Basis) where
  plus := ![v4671_pa,v4671_pb,v4671_pg]
  minus := ![(Primitive.Addresses.material4671 1).one,v4671_mb,v4671_mg]
  upper := v4671_upper
  lower := (Primitive.Addresses.material4671 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4671_pa_checked.trans (by decide +kernel)
    · exact v4671_pb_checked.trans (by decide +kernel)
    · exact v4671_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 84 94 Primitive.Addresses.material4671
    · exact v4671_mb_checked.trans (by decide +kernel)
    · exact v4671_mg_checked.trans (by decide +kernel)
  upper_error := v4671_upper_checked
  lower_error := reuse_lower_error 84 94 Primitive.Addresses.material4671

def v4672_pa : Scalar.QComplex := ((999996541402464618229546942614 : Int)/10^30,(-2630053822427713960500636520 : Int)/10^30)
theorem v4672_pa_checked : Scalar.distance (sourceCoefficient 84 95 1 0) v4672_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4672_pb : Scalar.QComplex := ((-1134809083743463765830426 : Int)/10^30,(-431476021220000449079947356 : Int)/10^30)
theorem v4672_pb_checked : Scalar.distance (sourceCoefficient 84 95 1 1) v4672_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4672_pg : Scalar.QComplex := ((-93086107142310550346726 : Int)/10^30,(244822318646417465354 : Int)/10^30)
theorem v4672_pg_checked : Scalar.distance (sourceCoefficient 84 95 1 2) v4672_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4672_mb : Scalar.QComplex := ((-1507153034556428522278602 : Int)/10^30,(-431474881272628953778264168 : Int)/10^30)
theorem v4672_mb_checked : Scalar.distance (sourceCoefficient 84 95 3 1) v4672_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4672_mg : Scalar.QComplex := ((-93085861211464012058927 : Int)/10^30,(325151345509058401964 : Int)/10^30)
theorem v4672_mg_checked : Scalar.distance (sourceCoefficient 84 95 3 2) v4672_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4672_upper : Scalar.QComplex := ((999990512790783153399556400286 : Int)/10^30,(-4355953216754568941121558536 : Int)/10^30)
theorem v4672_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 84 95 5) 1) 14) v4672_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4672 : Material (84 : Basis) (95 : Basis) where
  plus := ![v4672_pa,v4672_pb,v4672_pg]
  minus := ![(Primitive.Addresses.material4672 1).one,v4672_mb,v4672_mg]
  upper := v4672_upper
  lower := (Primitive.Addresses.material4672 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4672_pa_checked.trans (by decide +kernel)
    · exact v4672_pb_checked.trans (by decide +kernel)
    · exact v4672_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 84 95 Primitive.Addresses.material4672
    · exact v4672_mb_checked.trans (by decide +kernel)
    · exact v4672_mg_checked.trans (by decide +kernel)
  upper_error := v4672_upper_checked
  lower_error := reuse_lower_error 84 95 Primitive.Addresses.material4672

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
