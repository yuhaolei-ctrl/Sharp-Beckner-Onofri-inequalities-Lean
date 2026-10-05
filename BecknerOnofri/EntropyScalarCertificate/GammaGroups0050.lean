module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0062
public import BecknerOnofri.EntropyScalarCertificate.Bessel0063
public import BecknerOnofri.EntropyScalarCertificate.Bessel0520
public import BecknerOnofri.EntropyScalarCertificate.Brackets0025
public import BecknerOnofri.EntropyScalarCertificate.Logs0050
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0400
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (1377917519872925973020661439454081300069/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1377917519872925973020661439454081300069/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (172496873275287112989187080232432345033/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (172496873275287112989187080232432345033/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (2757892506075222876934158081313540060333/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2757892506075222876934158081313540060333/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0400 BracketBatch0025.bracket0401 (2757892506075222876934158081313540060333/20000000000000000000000000000000000000000) (272080686038203755817257864330998023/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0400 BracketBatch0025.bracket0401
  (2757892506075222876934158081313540060333/20000000000000000000000000000000000000000) (272080686038203755817257864330998023/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0400
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0401
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1379974986202296903913496641859458760261/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1379974986202296903913496641859458760261/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (55281305016585065060887666361995577197/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (55281305016585065060887666361995577197/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (1381003805808461765217844150454674095093/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1381003805808461765217844150454674095093/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0401 BracketBatch0025.bracket0402 (1381003805808461765217844150454674095093/10000000000000000000000000000000000000000) (273687327726457440065042146323417577/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0401 BracketBatch0025.bracket0402
  (1381003805808461765217844150454674095093/10000000000000000000000000000000000000000) (273687327726457440065042146323417577/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0401
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0402
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (691016312707313313261095829524944714961/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (691016312707313313261095829524944714961/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (276818087557956343835124551599952812933/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (276818087557956343835124551599952812933/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (2766123063204408345697814417049653494587/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2766123063204408345697814417049653494587/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0402 BracketBatch0025.bracket0403 (2766123063204408345697814417049653494587/20000000000000000000000000000000000000000) (275301090971033942072536225257257253/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0402 BracketBatch0025.bracket0403
  (2766123063204408345697814417049653494587/20000000000000000000000000000000000000000) (275301090971033942072536225257257253/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0402
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0403
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0062.rows BesselBatch0062.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (692045218894890859587811378999882032331/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (692045218894890859587811378999882032331/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (6930742118038764514507199160893366603/50000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6930742118038764514507199160893366603/50000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (1385119430698767311038531295089218692631/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1385119430698767311038531295089218692631/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0403 BracketBatch0025.bracket0404 (1385119430698767311038531295089218692631/10000000000000000000000000000000000000000) (27692199702590075343108443195692331/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0403 BracketBatch0025.bracket0404
  (1385119430698767311038531295089218692631/10000000000000000000000000000000000000000) (27692199702590075343108443195692331/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0403
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0404
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1386148423607752902901439832178673320597/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1386148423607752902901439832178673320597/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (277641316629731053723020582881314891949/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (277641316629731053723020582881314891949/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (1387177503378204085758271373292623890171/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1387177503378204085758271373292623890171/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0404 BracketBatch0025.bracket0405 (1387177503378204085758271373292623890171/10000000000000000000000000000000000000000) (139275033589242818023595940757269049/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0404 BracketBatch0025.bracket0405
  (1387177503378204085758271373292623890171/10000000000000000000000000000000000000000) (139275033589242818023595940757269049/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0404
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0405
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (694103291574327634307551457203287229871/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (694103291574327634307551457203287229871/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (43445778646647765766504366902436476517/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (43445778646647765766504366902436476517/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (1389235749920691886571621327642270854143/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1389235749920691886571621327642270854143/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0405 BracketBatch0025.bracket0406 (1389235749920691886571621327642270854143/10000000000000000000000000000000000000000) (280185322749687518120621029265314919/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0405 BracketBatch0025.bracket0406
  (1389235749920691886571621327642270854143/10000000000000000000000000000000000000000) (280185322749687518120621029265314919/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0405
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0406
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (1390264916692728504528139740877967248541/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1390264916692728504528139740877967248541/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (696161712260168561888043840269389666599/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (696161712260168561888043840269389666599/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (2782588341213065628304227421416746581739/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2782588341213065628304227421416746581739/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0406 BracketBatch0025.bracket0407 (2782588341213065628304227421416746581739/20000000000000000000000000000000000000000) (28182778509388740934291145828416373/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0406 BracketBatch0025.bracket0407
  (2782588341213065628304227421416746581739/20000000000000000000000000000000000000000) (28182778509388740934291145828416373/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0406
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0407
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (278464684904067424755217536107755866639/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (278464684904067424755217536107755866639/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0063.rows BesselBatch0063.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1394382106911970692266584061872930700503/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1394382106911970692266584061872930700503/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0520.rows BesselBatch0520.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (1393352765716153908021335871205855016849/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1393352765716153908021335871205855016849/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0050.rows ScalarLogs0050.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0025.bracket0407 BracketBatch0025.bracket0408 (1393352765716153908021335871205855016849/10000000000000000000000000000000000000000) (141738737799479667666087815022394263/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0025.bracket0407 BracketBatch0025.bracket0408
  (1393352765716153908021335871205855016849/10000000000000000000000000000000000000000) (141738737799479667666087815022394263/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0407
