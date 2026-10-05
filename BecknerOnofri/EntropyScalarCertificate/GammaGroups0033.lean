module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0041
public import BecknerOnofri.EntropyScalarCertificate.Bessel0042
public import BecknerOnofri.EntropyScalarCertificate.Bessel0509
public import BecknerOnofri.EntropyScalarCertificate.Bessel0510
public import BecknerOnofri.EntropyScalarCertificate.Brackets0016
public import BecknerOnofri.EntropyScalarCertificate.Brackets0017
public import BecknerOnofri.EntropyScalarCertificate.Logs0033
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0264
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (549797249916827252212385319896371844909/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (549797249916827252212385319896371844909/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (550815505707133842893266869636483882289/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (550815505707133842893266869636483882289/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (550306377811980547552826094766427863599/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (550306377811980547552826094766427863599/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨7,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨15,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0264 BracketBatch0016.bracket0265 (550306377811980547552826094766427863599/5000000000000000000000000000000000000000) (13913458101327831220024172451835469/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0264 BracketBatch0016.bracket0265
  (550306377811980547552826094766427863599/5000000000000000000000000000000000000000) (13913458101327831220024172451835469/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0264
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0265
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (44065240456570707431461349570918710583/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (44065240456570707431461349570918710583/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (551833829439108887822794153754344598529/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (551833829439108887822794153754344598529/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (2205298670292485461432122046781656961633/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2205298670292485461432122046781656961633/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨23,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨31,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0265 BracketBatch0016.bracket0266 (2205298670292485461432122046781656961633/20000000000000000000000000000000000000000) (22425918452627346476153888000863327/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0265 BracketBatch0016.bracket0266
  (2205298670292485461432122046781656961633/20000000000000000000000000000000000000000) (22425918452627346476153888000863327/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0265
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0266
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (220733531775643555129117661501737839411/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (220733531775643555129117661501737839411/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (1105704442490517110973273979829083020077/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1105704442490517110973273979829083020077/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (552343025342183721654715571834443054283/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (552343025342183721654715571834443054283/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨39,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨47,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0266 BracketBatch0016.bracket0267 (552343025342183721654715571834443054283/5000000000000000000000000000000000000000) (14119507257360851335325659621622717/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0266 BracketBatch0016.bracket0267
  (552343025342183721654715571834443054283/5000000000000000000000000000000000000000) (14119507257360851335325659621622717/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0266
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0267
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (552852221245258555486636989914541510037/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (552852221245258555486636989914541510037/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1107741362516273127437825978826637491289/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1107741362516273127437825978826637491289/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (2213445805006790238411099958655720511363/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2213445805006790238411099958655720511363/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨55,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨63,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0267 BracketBatch0016.bracket0268 (2213445805006790238411099958655720511363/20000000000000000000000000000000000000000) (22757415798947290110442900880659041/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0267 BracketBatch0016.bracket0268
  (2213445805006790238411099958655720511363/20000000000000000000000000000000000000000) (22757415798947290110442900880659041/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0267
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0268
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0041.rows BesselBatch0041.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (553870681258136563718912989413318745643/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (553870681258136563718912989413318745643/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (277444604805172140203178383394363540521/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (277444604805172140203178383394363540521/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (221751978173696168825053951240409165337/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (221751978173696168825053951240409165337/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨71,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨79,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0268 BracketBatch0016.bracket0269 (221751978173696168825053951240409165337/2000000000000000000000000000000000000000) (2865566797492509474818565226518897/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0268 BracketBatch0016.bracket0269
  (221751978173696168825053951240409165337/2000000000000000000000000000000000000000) (2865566797492509474818565226518897/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0268
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0269
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1109778419220688560812713533577454162081/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1109778419220688560812713533577454162081/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (555907806434530824273586621232363155091/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (555907806434530824273586621232363155091/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0509.rows BesselBatch0509.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (2221594032089750209359886776042180472263/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2221594032089750209359886776042180472263/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨87,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨95,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0269 BracketBatch0016.bracket0270 (2221594032089750209359886776042180472263/20000000000000000000000000000000000000000) (115462853634952900136568091295973641/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0269 BracketBatch0016.bracket0270
  (2221594032089750209359886776042180472263/20000000000000000000000000000000000000000) (115462853634952900136568091295973641/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0269
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0270
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1111815612869061648547173242464726310179/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1111815612869061648547173242464726310179/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (556926471863393165749659004827230952519/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (556926471863393165749659004827230952519/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (2225668556595847980046491252119188215217/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2225668556595847980046491252119188215217/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨103,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨111,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0270 BracketBatch0016.bracket0271 (2225668556595847980046491252119188215217/20000000000000000000000000000000000000000) (116307641093836328614743362157156559/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0270 BracketBatch0016.bracket0271
  (2225668556595847980046491252119188215217/20000000000000000000000000000000000000000) (116307641093836328614743362157156559/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0270
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0271
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (222770588745357266299863601930892381007/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (222770588745357266299863601930892381007/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1115890412059352455832202694445391467609/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1115890412059352455832202694445391467609/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (557435838946534696832880176024963343161/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (557435838946534696832880176024963343161/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨119,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0033.rows ScalarLogs0033.accepted ⟨127,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0016.bracket0271 BracketBatch0017.bracket0272 (557435838946534696832880176024963343161/5000000000000000000000000000000000000000) (29289262800467360073749045155911091/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0016.bracket0271 BracketBatch0017.bracket0272
  (557435838946534696832880176024963343161/5000000000000000000000000000000000000000) (29289262800467360073749045155911091/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0271
