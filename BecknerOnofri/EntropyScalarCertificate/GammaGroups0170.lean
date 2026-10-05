import BecknerOnofri.EntropyScalarCertificate.Bessel0212
import BecknerOnofri.EntropyScalarCertificate.Bessel0213
import BecknerOnofri.EntropyScalarCertificate.Bessel0595
import BecknerOnofri.EntropyScalarCertificate.Brackets0085
import BecknerOnofri.EntropyScalarCertificate.Logs0170
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1360
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (3157701984244112418745186510143397998469/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3157701984244112418745186510143397998469/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (7913257076835883780927941231476439185993/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7913257076835883780927941231476439185993/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (31615024074892329655581815013669868364331/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (31615024074892329655581815013669868364331/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1360 BracketBatch0085.bracket1361 (31615024074892329655581815013669868364331/20000000000000000000000000000000000000000) (286589116120573402006807749056842199089/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1360 BracketBatch0085.bracket1361
  (31615024074892329655581815013669868364331/20000000000000000000000000000000000000000) (286589116120573402006807749056842199089/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1360
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1361
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (15826514153671767561855882462952878371983/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15826514153671767561855882462952878371983/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (3172944867431004446317023838872859070641/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3172944867431004446317023838872859070641/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (7922809622706697448360250414329293431297/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7922809622706697448360250414329293431297/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1361 BracketBatch0085.bracket1362 (7922809622706697448360250414329293431297/5000000000000000000000000000000000000000) (575313553158387258919320424390471805059/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1361 BracketBatch0085.bracket1362
  (7922809622706697448360250414329293431297/5000000000000000000000000000000000000000) (575313553158387258919320424390471805059/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1361
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1362
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (7932362168577511115792559597182147676601/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7932362168577511115792559597182147676601/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (15903142343594819250353894674585280201087/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15903142343594819250353894674585280201087/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (31767866680749841481939013868949575554289/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (31767866680749841481939013868949575554289/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1362 BracketBatch0085.bracket1363 (31767866680749841481939013868949575554289/20000000000000000000000000000000000000000) (577458908457277889626141448800052764269/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1362 BracketBatch0085.bracket1363
  (31767866680749841481939013868949575554289/20000000000000000000000000000000000000000) (577458908457277889626141448800052764269/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1362
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1363
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0212.rows BesselBatch0212.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (3975785585898704812588473668646320050271/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3975785585898704812588473668646320050271/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (15941770067075610485470941300839375021493/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15941770067075610485470941300839375021493/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (31844912410670429735824835975424655222577/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (31844912410670429735824835975424655222577/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1363 BracketBatch0085.bracket1364 (31844912410670429735824835975424655222577/20000000000000000000000000000000000000000) (579614368313142767977246844774427924007/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1363 BracketBatch0085.bracket1364
  (31844912410670429735824835975424655222577/20000000000000000000000000000000000000000) (579614368313142767977246844774427924007/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1363
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1364
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1594177006707561048547094130083937502149/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1594177006707561048547094130083937502149/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (249697022252446395350992144286532973567/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (249697022252446395350992144286532973567/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (15961189745616089893967219267588742664889/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15961189745616089893967219267588742664889/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1364 BracketBatch0085.bracket1365 (15961189745616089893967219267588742664889/10000000000000000000000000000000000000000) (290890001773759741539386113460260401183/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1364 BracketBatch0085.bracket1365
  (15961189745616089893967219267588742664889/10000000000000000000000000000000000000000) (290890001773759741539386113460260401183/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1364
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1365
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (3196121884831313860492699446867622061657/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3196121884831313860492699446867622061657/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (16019662354191511072680002727067468492963/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16019662354191511072680002727067468492963/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (1000008493073377511723234373793924337539/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1000008493073377511723234373793924337539/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1365 BracketBatch0085.bracket1366 (1000008493073377511723234373793924337539/625000000000000000000000000000000000000) (583955885634639068737021854062636966179/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1365 BracketBatch0085.bracket1366
  (1000008493073377511723234373793924337539/625000000000000000000000000000000000000) (583955885634639068737021854062636966179/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1365
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1366
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (100122889713696944204250017044171678081/62500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (100122889713696944204250017044171678081/62500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (4014732704913516973834815283089928048469/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4014732704913516973834815283089928048469/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (8019648293461394742004815964856795171709/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8019648293461394742004815964856795171709/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1366 BracketBatch0085.bracket1367 (8019648293461394742004815964856795171709/5000000000000000000000000000000000000000) (586142086707967421863128441048082402693/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1366 BracketBatch0085.bracket1367
  (8019648293461394742004815964856795171709/5000000000000000000000000000000000000000) (586142086707967421863128441048082402693/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1366
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1367
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (16058930819654067895339261132359712193873/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16058930819654067895339261132359712193873/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0213.rows BesselBatch0213.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (4024604201617054027008221921537405125371/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4024604201617054027008221921537405125371/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0595.rows BesselBatch0595.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (32157347626122284003372148818509332695357/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (32157347626122284003372148818509332695357/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0170.rows ScalarLogs0170.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0085.bracket1367 BracketBatch0085.bracket1368 (32157347626122284003372148818509332695357/20000000000000000000000000000000000000000) (147084669891702175231810685844730456663/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0085.bracket1367 BracketBatch0085.bracket1368
  (32157347626122284003372148818509332695357/20000000000000000000000000000000000000000) (147084669891702175231810685844730456663/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1367
