module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0015
public import BecknerOnofri.EntropyScalarCertificate.Bessel0016
public import BecknerOnofri.EntropyScalarCertificate.Bessel0496
public import BecknerOnofri.EntropyScalarCertificate.Bessel0497
public import BecknerOnofri.EntropyScalarCertificate.Brackets0006
public import BecknerOnofri.EntropyScalarCertificate.Logs0012
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0096
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (759179404993919178510607210402210606771/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (759179404993919178510607210402210606771/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (47574798783435221125842164862642080313/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (47574798783435221125842164862642080313/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (1520376185528882716524081848204483891779/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1520376185528882716524081848204483891779/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0096 BracketBatch0006.bracket0097 (1520376185528882716524081848204483891779/20000000000000000000000000000000000000000) (2523438320307429692900327256071523/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0096 BracketBatch0006.bracket0097
  (1520376185528882716524081848204483891779/20000000000000000000000000000000000000000) (2523438320307429692900327256071523/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0096
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0097
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (152239356106992707602694927560454657001/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (152239356106992707602694927560454657001/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (152642849726083242921243096508618932231/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (152642849726083242921243096508618932231/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (19055137864567246907746126504317099327/250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19055137864567246907746126504317099327/250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0097 BracketBatch0006.bracket0098 (19055137864567246907746126504317099327/250000000000000000000000000000000000000) (6376680726266691460251012906976573/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0097 BracketBatch0006.bracket0098
  (19055137864567246907746126504317099327/250000000000000000000000000000000000000) (6376680726266691460251012906976573/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0097
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0098
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (23850445269700506706444233829471708161/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (23850445269700506706444233829471708161/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (382615904766027105953419600032467336567/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (382615904766027105953419600032467336567/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (764223029081235213256527341304014667143/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (764223029081235213256527341304014667143/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0098 BracketBatch0006.bracket0099 (764223029081235213256527341304014667143/10000000000000000000000000000000000000000) (12890614654978695958199315193850363/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0098 BracketBatch0006.bracket0099
  (764223029081235213256527341304014667143/10000000000000000000000000000000000000000) (12890614654978695958199315193850363/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0098
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0099
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (765231809532054211906839200064934673131/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (765231809532054211906839200064934673131/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (191812365872929451990758009252125850739/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (191812365872929451990758009252125850739/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (1532481273023772019869871237073438076087/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1532481273023772019869871237073438076087/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0099 BracketBatch0006.bracket0100 (1532481273023772019869871237073438076087/20000000000000000000000000000000000000000) (5211582783820714303798748375419097/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0099 BracketBatch0006.bracket0100
  (1532481273023772019869871237073438076087/20000000000000000000000000000000000000000) (5211582783820714303798748375419097/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0099
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0100
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (767249463491717807963032037008503402953/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (767249463491717807963032037008503402953/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (384633605380655367224407200839773732063/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (384633605380655367224407200839773732063/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (1536516674253028542411846438688050867079/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1536516674253028542411846438688050867079/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0100 BracketBatch0006.bracket0101 (1536516674253028542411846438688050867079/20000000000000000000000000000000000000000) (6584197066209466297827604170297937/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0100 BracketBatch0006.bracket0101
  (1536516674253028542411846438688050867079/20000000000000000000000000000000000000000) (6584197066209466297827604170297937/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0100
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0101
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (769267210761310734448814401679547464123/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (769267210761310734448814401679547464123/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (192821262898200088991419608171426560759/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (192821262898200088991419608171426560759/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (1540552262354111090414492834365253707159/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1540552262354111090414492834365253707159/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0101 BracketBatch0006.bracket0102 (1540552262354111090414492834365253707159/20000000000000000000000000000000000000000) (3327232988809205393455240648853237/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0101 BracketBatch0006.bracket0102
  (1540552262354111090414492834365253707159/20000000000000000000000000000000000000000) (3327232988809205393455240648853237/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0101
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0102
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (771285051592800355965678432685706243033/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (771285051592800355965678432685706243033/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (773302986238217849448518039797197986929/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (773302986238217849448518039797197986929/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (772294018915509102707098236241452114981/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (772294018915509102707098236241452114981/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0102 BracketBatch0006.bracket0103 (772294018915509102707098236241452114981/10000000000000000000000000000000000000000) (6725288112577686629743707853272281/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0102 BracketBatch0006.bracket0103
  (772294018915509102707098236241452114981/10000000000000000000000000000000000000000) (6725288112577686629743707853272281/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0102
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0103
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (386651493119108924724259019898598993463/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (386651493119108924724259019898598993463/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (387660507474829191838332003067258612823/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (387660507474829191838332003067258612823/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (387156000296969058281295511482928803143/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (387156000296969058281295511482928803143/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0012.rows ScalarLogs0012.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0103 BracketBatch0006.bracket0104 (387156000296969058281295511482928803143/5000000000000000000000000000000000000000) (5437333101928232871464816506129613/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0103 BracketBatch0006.bracket0104
  (387156000296969058281295511482928803143/5000000000000000000000000000000000000000) (5437333101928232871464816506129613/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0103
