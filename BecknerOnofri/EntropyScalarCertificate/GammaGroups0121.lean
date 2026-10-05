import BecknerOnofri.EntropyScalarCertificate.Bessel0151
import BecknerOnofri.EntropyScalarCertificate.Bessel0152
import BecknerOnofri.EntropyScalarCertificate.Bessel0564
import BecknerOnofri.EntropyScalarCertificate.Bessel0565
import BecknerOnofri.EntropyScalarCertificate.Brackets0060
import BecknerOnofri.EntropyScalarCertificate.Brackets0061
import BecknerOnofri.EntropyScalarCertificate.Logs0121
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0968
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (5051104739876870082557900384020746197351/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5051104739876870082557900384020746197351/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (5065320031844247120754742046124935097037/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5065320031844247120754742046124935097037/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (2529106192930279300828160607536420323597/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2529106192930279300828160607536420323597/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0968 BracketBatch0060.bracket0969 (2529106192930279300828160607536420323597/5000000000000000000000000000000000000000) (34909212816270217435824038908520887243/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0968 BracketBatch0060.bracket0969
  (2529106192930279300828160607536420323597/5000000000000000000000000000000000000000) (34909212816270217435824038908520887243/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0968
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0969
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (2532660015922123560377371023062467548517/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2532660015922123560377371023062467548517/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (5079561180036468936463721835575460416617/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5079561180036468936463721835575460416617/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (10144881211880716057218463881700395513651/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10144881211880716057218463881700395513651/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0969 BracketBatch0060.bracket0970 (10144881211880716057218463881700395513651/20000000000000000000000000000000000000000) (2202279007843829946053069400712806413/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0969 BracketBatch0060.bracket0970
  (10144881211880716057218463881700395513651/20000000000000000000000000000000000000000) (2202279007843829946053069400712806413/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0969
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0970
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (2539780590018234468231860917787730208307/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2539780590018234468231860917787730208307/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (509382832779455950805118406723598198033/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (509382832779455950805118406723598198033/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (635836844239439277782181618925715149809/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (635836844239439277782181618925715149809/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0970 BracketBatch0060.bracket0971 (635836844239439277782181618925715149809/1250000000000000000000000000000000000000) (35566137059733098025920749700642860837/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0970 BracketBatch0060.bracket0971
  (635836844239439277782181618925715149809/1250000000000000000000000000000000000000) (35566137059733098025920749700642860837/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0970
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0971
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (5093828327794559508051184067235981980327/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5093828327794559508051184067235981980327/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (5108121619439364947164419849129660515129/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5108121619439364947164419849129660515129/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (318810935851060139225487622386426327983/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (318810935851060139225487622386426327983/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0971 BracketBatch0060.bracket0972 (318810935851060139225487622386426327983/625000000000000000000000000000000000000) (1794912277839922559430395221205504859/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0971 BracketBatch0060.bracket0972
  (318810935851060139225487622386426327983/625000000000000000000000000000000000000) (1794912277839922559430395221205504859/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0971
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0972
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0151.rows BesselBatch0151.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (2554060809719682473582209924564830257563/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2554060809719682473582209924564830257563/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (128061030007018375719654947172063884487/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (128061030007018375719654947172063884487/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (5115281409860049987975308868006107947303/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5115281409860049987975308868006107947303/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0972 BracketBatch0060.bracket0973 (5115281409860049987975308868006107947303/10000000000000000000000000000000000000000) (36232803624495881106500361439425229841/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0972 BracketBatch0060.bracket0973
  (5115281409860049987975308868006107947303/10000000000000000000000000000000000000000) (36232803624495881106500361439425229841/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0972
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0973
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (5122441200280735028786197886882555379477/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5122441200280735028786197886882555379477/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (513678721662680842743421700313006202177/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (513678721662680842743421700313006202177/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0564.rows BesselBatch0564.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (10259228416907543456220414890012617401247/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10259228416907543456220414890012617401247/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0973 BracketBatch0060.bracket0974 (10259228416907543456220414890012617401247/20000000000000000000000000000000000000000) (914245633526357184127774443315269013/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0973 BracketBatch0060.bracket0974
  (10259228416907543456220414890012617401247/20000000000000000000000000000000000000000) (914245633526357184127774443315269013/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0973
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0974
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (5136787216626808427434217003130062021767/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5136787216626808427434217003130062021767/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (515115981579340305120968250888595134941/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (515115981579340305120968250888595134941/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (10287947032420211478643899512016013371177/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10287947032420211478643899512016013371177/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0974 BracketBatch0060.bracket0975 (10287947032420211478643899512016013371177/20000000000000000000000000000000000000000) (18454662427801176968299523427581066057/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0974 BracketBatch0060.bracket0975
  (10287947032420211478643899512016013371177/20000000000000000000000000000000000000000) (18454662427801176968299523427581066057/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0974
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0975
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (5151159815793403051209682508885951349407/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5151159815793403051209682508885951349407/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (2582779573056756443423994063104861030549/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2582779573056756443423994063104861030549/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (2063343792381383187611534127019134682101/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2063343792381383187611534127019134682101/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0121.rows ScalarLogs0121.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0060.bracket0975 BracketBatch0061.bracket0976 (2063343792381383187611534127019134682101/4000000000000000000000000000000000000000) (37251316388642875009199369376800525413/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0060.bracket0975 BracketBatch0061.bracket0976
  (2063343792381383187611534127019134682101/4000000000000000000000000000000000000000) (37251316388642875009199369376800525413/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0975
