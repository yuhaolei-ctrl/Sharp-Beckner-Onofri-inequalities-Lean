module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0225
public import BecknerOnofri.EntropyScalarCertificate.Bessel0226
public import BecknerOnofri.EntropyScalarCertificate.Bessel0601
public import BecknerOnofri.EntropyScalarCertificate.Bessel0602
public import BecknerOnofri.EntropyScalarCertificate.Brackets0090
public import BecknerOnofri.EntropyScalarCertificate.Logs0180
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1440
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (266320109295046737466063324016375688041/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (266320109295046737466063324016375688041/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (852675313108294677598714576996830809049/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (852675313108294677598714576996830809049/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (8524498314262221187450586069246165053901/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8524498314262221187450586069246165053901/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1440 BracketBatch0090.bracket1441 (8524498314262221187450586069246165053901/5000000000000000000000000000000000000000) (644462102642035249001243407680920513659/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1440 BracketBatch0090.bracket1441
  (8524498314262221187450586069246165053901/5000000000000000000000000000000000000000) (644462102642035249001243407680920513659/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1440
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1441
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (17053506262165893551974291539936616180977/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17053506262165893551974291539936616180977/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (17062536413869632645713504326890821956947/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17062536413869632645713504326890821956947/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (8529010669008881549421948966706859534481/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8529010669008881549421948966706859534481/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1441 BracketBatch0090.bracket1442 (8529010669008881549421948966706859534481/5000000000000000000000000000000000000000) (322479141665855734933804976985359615243/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1441 BracketBatch0090.bracket1442
  (8529010669008881549421948966706859534481/5000000000000000000000000000000000000000) (322479141665855734933804976985359615243/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1441
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1442
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1066408525866852040357094020430676372309/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1066408525866852040357094020430676372309/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (2133947183919704440358967573186540417387/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2133947183919704440358967573186540417387/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (853352847130681704214631122809578632401/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (853352847130681704214631122809578632401/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1442 BracketBatch0090.bracket1443 (853352847130681704214631122809578632401/500000000000000000000000000000000000000) (80681870461078049146662431404749498783/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1442 BracketBatch0090.bracket1443
  (853352847130681704214631122809578632401/500000000000000000000000000000000000000) (80681870461078049146662431404749498783/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1442
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1443
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (17071577471357635522871740585492323339093/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17071577471357635522871740585492323339093/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (8540314728023615545312136573723828692059/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8540314728023615545312136573723828692059/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (34152206927404866613496013732939980723211/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34152206927404866613496013732939980723211/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1443 BracketBatch0090.bracket1444 (34152206927404866613496013732939980723211/20000000000000000000000000000000000000000) (645952144452517759046603286064581287797/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1443 BracketBatch0090.bracket1444
  (34152206927404866613496013732939980723211/20000000000000000000000000000000000000000) (645952144452517759046603286064581287797/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1443
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1444
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (3416125891209446218124854629489531476823/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3416125891209446218124854629489531476823/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (1068105774338113277795547138317191858909/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1068105774338113277795547138317191858909/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (34170321845457043535353027360522727126659/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34170321845457043535353027360522727126659/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1444 BracketBatch0090.bracket1445 (34170321845457043535353027360522727126659/20000000000000000000000000000000000000000) (323224913182257448156233946008187204323/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1444 BracketBatch0090.bracket1445
  (34170321845457043535353027360522727126659/20000000000000000000000000000000000000000) (323224913182257448156233946008187204323/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1444
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1445
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (17089692389409812444728754213075069742541/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17089692389409812444728754213075069742541/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (8549383146485499881021271434211432988179/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8549383146485499881021271434211432988179/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (34188458682380812206771297081497935718899/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34188458682380812206771297081497935718899/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1445 BracketBatch0090.bracket1446 (34188458682380812206771297081497935718899/20000000000000000000000000000000000000000) (161737002541780360797075556051058958329/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1445 BracketBatch0090.bracket1446
  (34188458682380812206771297081497935718899/20000000000000000000000000000000000000000) (161737002541780360797075556051058958329/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1445
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1446
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (3419753258594199952408508573684573195271/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3419753258594199952408508573684573195271/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (4276962797077700940657955742159856693619/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4276962797077700940657955742159856693619/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (34206617481281803524674365837062292750831/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34206617481281803524674365837062292750831/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1446 BracketBatch0090.bracket1447 (34206617481281803524674365837062292750831/20000000000000000000000000000000000000000) (64744669660422807326362317013211057219/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1446 BracketBatch0090.bracket1447
  (34206617481281803524674365837062292750831/20000000000000000000000000000000000000000) (64744669660422807326362317013211057219/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1446
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1447
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (17107851188310803762631822968639426774473/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17107851188310803762631822968639426774473/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (4279236774265947435947818472755730580887/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4279236774265947435947818472755730580887/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (34224798285374593506423096859662349098021/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34224798285374593506423096859662349098021/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0180.rows ScalarLogs0180.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1447 BracketBatch0090.bracket1448 (34224798285374593506423096859662349098021/20000000000000000000000000000000000000000) (129589177284222645355386090366927521293/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1447 BracketBatch0090.bracket1448
  (34224798285374593506423096859662349098021/20000000000000000000000000000000000000000) (129589177284222645355386090366927521293/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1447
