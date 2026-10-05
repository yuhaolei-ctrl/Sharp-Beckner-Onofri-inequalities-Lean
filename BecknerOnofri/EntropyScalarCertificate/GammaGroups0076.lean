module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0095
public import BecknerOnofri.EntropyScalarCertificate.Bessel0096
public import BecknerOnofri.EntropyScalarCertificate.Bessel0536
public import BecknerOnofri.EntropyScalarCertificate.Bessel0537
public import BecknerOnofri.EntropyScalarCertificate.Brackets0038
public import BecknerOnofri.EntropyScalarCertificate.Logs0076
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0608
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (905008093463077120587089620431324197897/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (905008093463077120587089620431324197897/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (1812115839333703403100495243689147503971/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1812115839333703403100495243689147503971/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (724426405251971528854934896910359179953/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (724426405251971528854934896910359179953/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0608 BracketBatch0038.bracket0609 (724426405251971528854934896910359179953/4000000000000000000000000000000000000000) (198389032062759750589854736520003321/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0608 BracketBatch0038.bracket0609
  (724426405251971528854934896910359179953/4000000000000000000000000000000000000000) (198389032062759750589854736520003321/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0608
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0609
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (56628619979178231346890476365285859499/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (56628619979178231346890476365285859499/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (453553931465742090891581001778756257483/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (453553931465742090891581001778756257483/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (36263315651966717666668192508041725339/200000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36263315651966717666668192508041725339/200000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0609 BracketBatch0038.bracket0610 (36263315651966717666668192508041725339/200000000000000000000000000000000000000) (398575935016988407909423488324569273/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0609 BracketBatch0038.bracket0610
  (36263315651966717666668192508041725339/200000000000000000000000000000000000000) (398575935016988407909423488324569273/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0609
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0610
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1814215725862968363566324007115025029929/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1814215725862968363566324007115025029929/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1816315846824889889070616250616272462143/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1816315846824889889070616250616272462143/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (453816446585982281579617532216412186509/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (453816446585982281579617532216412186509/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0610 BracketBatch0038.bracket0611 (453816446585982281579617532216412186509/2500000000000000000000000000000000000000) (200189972909132147069773915947545323/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0610 BracketBatch0038.bracket0611
  (453816446585982281579617532216412186509/2500000000000000000000000000000000000000) (200189972909132147069773915947545323/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0610
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0611
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (90815792341244494453530812530813623107/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (90815792341244494453530812530813623107/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (1818416202530585608679108801959102449259/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1818416202530585608679108801959102449259/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (3634732049355475497749725052575374911399/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3634732049355475497749725052575374911399/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0611 BracketBatch0038.bracket0612 (3634732049355475497749725052575374911399/20000000000000000000000000000000000000000) (201095055383712549265059197182141833/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0611 BracketBatch0038.bracket0612
  (3634732049355475497749725052575374911399/20000000000000000000000000000000000000000) (201095055383712549265059197182141833/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0611
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0612
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (227302025316323201084888600244887806157/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (227302025316323201084888600244887806157/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (1820516793291350297993093705262585943719/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1820516793291350297993093705262585943719/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (145557319832877436266888100288867535719/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (145557319832877436266888100288867535719/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0612 BracketBatch0038.bracket0613 (145557319832877436266888100288867535719/800000000000000000000000000000000000000) (808012888241260102467752935817482619/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0612 BracketBatch0038.bracket0613
  (145557319832877436266888100288867535719/800000000000000000000000000000000000000) (808012888241260102467752935817482619/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0612
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0613
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (455129198322837574498273426315646485929/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (455129198322837574498273426315646485929/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1822617619418656163452158125130869198883/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1822617619418656163452158125130869198883/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (3643134412710006461445251830393455142599/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3643134412710006461445251830393455142599/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0613 BracketBatch0038.bracket0614 (3643134412710006461445251830393455142599/20000000000000000000000000000000000000000) (202914480076063657856113556120626577/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0613 BracketBatch0038.bracket0614
  (3643134412710006461445251830393455142599/20000000000000000000000000000000000000000) (202914480076063657856113556120626577/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0613
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0614
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0095.rows BesselBatch0095.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (11391360121366601021575988282067932493/62500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11391360121366601021575988282067932493/62500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (1824718681224153126971552082905368359213/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1824718681224153126971552082905368359213/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (3647336300642809290423710208036237558093/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3647336300642809290423710208036237558093/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0614 BracketBatch0038.bracket0615 (3647336300642809290423710208036237558093/20000000000000000000000000000000000000000) (407657673154261642211117269124932073/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0614 BracketBatch0038.bracket0615
  (3647336300642809290423710208036237558093/20000000000000000000000000000000000000000) (407657673154261642211117269124932073/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0614
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0615
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (182471868122415312697155208290536835921/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (182471868122415312697155208290536835921/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0096.rows BesselBatch0096.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (913409989509834555457421122398158817457/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (913409989509834555457421122398158817457/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0536.rows BesselBatch0536.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (912884665060955559471598581925421498531/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (912884665060955559471598581925421498531/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0076.rows ScalarLogs0076.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0038.bracket0615 BracketBatch0038.bracket0616 (912884665060955559471598581925421498531/5000000000000000000000000000000000000000) (163797038974992813163572632491331857/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0038.bracket0615 BracketBatch0038.bracket0616
  (912884665060955559471598581925421498531/5000000000000000000000000000000000000000) (163797038974992813163572632491331857/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0615
