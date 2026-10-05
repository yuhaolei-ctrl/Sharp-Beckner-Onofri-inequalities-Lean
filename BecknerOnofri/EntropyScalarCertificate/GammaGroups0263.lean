import BecknerOnofri.EntropyScalarCertificate.Bessel0328
import BecknerOnofri.EntropyScalarCertificate.Bessel0329
import BecknerOnofri.EntropyScalarCertificate.Bessel0330
import BecknerOnofri.EntropyScalarCertificate.Bessel0653
import BecknerOnofri.EntropyScalarCertificate.Brackets0131
import BecknerOnofri.EntropyScalarCertificate.Brackets0132
import BecknerOnofri.EntropyScalarCertificate.Logs0263
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2104
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (34086364830065597555550601508049000183289/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (34086364830065597555550601508049000183289/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (17087926557327878596249301649325113351073/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17087926557327878596249301649325113351073/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (13652443588944270949609840961339845377087/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13652443588944270949609840961339845377087/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2104 BracketBatch0131.bracket2105 (13652443588944270949609840961339845377087/2000000000000000000000000000000000000000) (226361983409719960833329149401754024471/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2104 BracketBatch0131.bracket2105
  (13652443588944270949609840961339845377087/2000000000000000000000000000000000000000) (226361983409719960833329149401754024471/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2104
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2105
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (68351706229311514384997206597300453404289/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (68351706229311514384997206597300453404289/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (17132911610879686483179571929979215524467/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17132911610879686483179571929979215524467/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (136883352672830260317715494317217315502157/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (136883352672830260317715494317217315502157/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2105 BracketBatch0131.bracket2106 (136883352672830260317715494317217315502157/20000000000000000000000000000000000000000) (226699569661090515461501889681044431441/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2105 BracketBatch0131.bracket2106
  (136883352672830260317715494317217315502157/20000000000000000000000000000000000000000) (226699569661090515461501889681044431441/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2105
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2106
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (13706329288703749186543657543983372419573/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13706329288703749186543657543983372419573/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (34356279046744311394966313961563232197469/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (34356279046744311394966313961563232197469/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (137244204537007368722650915643043326492803/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (137244204537007368722650915643043326492803/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2106 BracketBatch0131.bracket2107 (137244204537007368722650915643043326492803/20000000000000000000000000000000000000000) (141898846650341836708470124399652713759/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2106 BracketBatch0131.bracket2107
  (137244204537007368722650915643043326492803/20000000000000000000000000000000000000000) (141898846650341836708470124399652713759/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2106
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2107
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (13742511618697724557986525584625292878987/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13742511618697724557986525584625292878987/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (68894449054185145823430277828226694162741/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (68894449054185145823430277828226694162741/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (34401751786918442153340726437838289639419/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34401751786918442153340726437838289639419/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2107 BracketBatch0131.bracket2108 (34401751786918442153340726437838289639419/5000000000000000000000000000000000000000) (2273777438545389367142400920335790730903/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2107 BracketBatch0131.bracket2108
  (34401751786918442153340726437838289639419/5000000000000000000000000000000000000000) (2273777438545389367142400920335790730903/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2107
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2108
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (34447224527092572911715138914113347081369/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (34447224527092572911715138914113347081369/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (34538663642970932605141073555693324416211/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (34538663642970932605141073555693324416211/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (3449294408503175275842810623490333574879/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3449294408503175275842810623490333574879/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2108 BracketBatch0131.bracket2109 (3449294408503175275842810623490333574879/500000000000000000000000000000000000000) (2277183428549978415756675935799024764519/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2108 BracketBatch0131.bracket2109
  (3449294408503175275842810623490333574879/500000000000000000000000000000000000000) (2277183428549978415756675935799024764519/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2108
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2109
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (69077327285941865210282147111386648832419/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (69077327285941865210282147111386648832419/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (69261200835621769980303387758460369095371/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (69261200835621769980303387758460369095371/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (13833852812156363519058553486984701792779/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13833852812156363519058553486984701792779/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2109 BracketBatch0131.bracket2110 (13833852812156363519058553486984701792779/2000000000000000000000000000000000000000) (2280599572398275008780456756694389062549/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2109 BracketBatch0131.bracket2110
  (13833852812156363519058553486984701792779/2000000000000000000000000000000000000000) (2280599572398275008780456756694389062549/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2109
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2110
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (8657650104452721247537923469807546136921/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8657650104452721247537923469807546136921/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (69446077837796140542290618665302528457111/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (69446077837796140542290618665302528457111/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (138707278673417910522594006423762897552479/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (138707278673417910522594006423762897552479/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2110 BracketBatch0131.bracket2111 (138707278673417910522594006423762897552479/20000000000000000000000000000000000000000) (285503240816752117466490418167613793963/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2110 BracketBatch0131.bracket2111
  (138707278673417910522594006423762897552479/20000000000000000000000000000000000000000) (285503240816752117466490418167613793963/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2110
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2111
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0329.rows BesselBatch0329.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (17361519459449035135572654666325632114277/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17361519459449035135572654666325632114277/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (34815983257971363436151800049280156931933/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (34815983257971363436151800049280156931933/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (69539022176869433707297109381931421160487/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (69539022176869433707297109381931421160487/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0263.rows ScalarLogs0263.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2111 BracketBatch0132.bracket2112 (69539022176869433707297109381931421160487/10000000000000000000000000000000000000000) (228746254787068178467664112724064615851/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2111 BracketBatch0132.bracket2112
  (69539022176869433707297109381931421160487/10000000000000000000000000000000000000000) (228746254787068178467664112724064615851/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2111
