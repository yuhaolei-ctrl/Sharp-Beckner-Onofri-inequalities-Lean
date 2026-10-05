import BecknerOnofri.EntropyScalarCertificate.Bessel0427
import BecknerOnofri.EntropyScalarCertificate.Bessel0428
import BecknerOnofri.EntropyScalarCertificate.Bessel0702
import BecknerOnofri.EntropyScalarCertificate.Bessel0703
import BecknerOnofri.EntropyScalarCertificate.Brackets0171
import BecknerOnofri.EntropyScalarCertificate.Logs0342
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2736
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (845850186121081458475131873201856958509261/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (845850186121081458475131873201856958509261/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (847279270673815802375451848496500093045757/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (847279270673815802375451848496500093045757/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (846564728397448630425291860849178525777509/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (846564728397448630425291860849178525777509/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2736 BracketBatch0171.bracket2737 (846564728397448630425291860849178525777509/10000000000000000000000000000000000000000) (1171232506373936481468090697121455746559/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2736 BracketBatch0171.bracket2737
  (846564728397448630425291860849178525777509/10000000000000000000000000000000000000000) (1171232506373936481468090697121455746559/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2736
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2737
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (423639635336907901187725924248250046522877/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (423639635336907901187725924248250046522877/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (106089149951683244814290165078900809812877/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (106089149951683244814290165078900809812877/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (169599247028728176088977316912770657154877/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (169599247028728176088977316912770657154877/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2737 BracketBatch0171.bracket2738 (169599247028728176088977316912770657154877/2000000000000000000000000000000000000000) (1464688234040314097713484910119889298363/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2737 BracketBatch0171.bracket2738
  (169599247028728176088977316912770657154877/2000000000000000000000000000000000000000) (1464688234040314097713484910119889298363/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2737
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2738
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (848713199613465958514321320631206478503013/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (848713199613465958514321320631206478503013/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (425075998807163681974570614808695164426609/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (425075998807163681974570614808695164426609/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (1698865197227793322463462550248596807356231/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1698865197227793322463462550248596807356231/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2738 BracketBatch0171.bracket2739 (1698865197227793322463462550248596807356231/20000000000000000000000000000000000000000) (2930673919851856437826213444331543040633/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2738 BracketBatch0171.bracket2739
  (1698865197227793322463462550248596807356231/20000000000000000000000000000000000000000) (2930673919851856437826213444331543040633/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2738
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2739
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0427.rows BesselBatch0427.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (170030399522865472789828245923478065770643/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (170030399522865472789828245923478065770643/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (851595689518547805744559624537914685229801/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (851595689518547805744559624537914685229801/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (212718460891609396211712606769413126760377/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (212718460891609396211712606769413126760377/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2739 BracketBatch0171.bracket2740 (212718460891609396211712606769413126760377/2500000000000000000000000000000000000000) (2931973628721693569189749344151195607737/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2739 BracketBatch0171.bracket2740
  (212718460891609396211712606769413126760377/2500000000000000000000000000000000000000) (2931973628721693569189749344151195607737/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2739
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2740
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (425797844759273902872279812268957342614899/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (425797844759273902872279812268957342614899/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (853044300337557168417154921561432970097421/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (853044300337557168417154921561432970097421/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0702.rows BesselBatch0702.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (1704639989856104974161714546099347655327219/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1704639989856104974161714546099347655327219/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2740 BracketBatch0171.bracket2741 (1704639989856104974161714546099347655327219/20000000000000000000000000000000000000000) (366659450274978470095136529650461071651/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2740 BracketBatch0171.bracket2741
  (1704639989856104974161714546099347655327219/20000000000000000000000000000000000000000) (366659450274978470095136529650461071651/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2740
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2741
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (426522150168778584208577460780716485048709/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (426522150168778584208577460780716485048709/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (854497855253511820432453805156025490440839/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (854497855253511820432453805156025490440839/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (1707542155591068988849608726717458460538257/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1707542155591068988849608726717458460538257/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2741 BracketBatch0171.bracket2742 (1707542155591068988849608726717458460538257/20000000000000000000000000000000000000000) (1173831939133080036561857522404355032423/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2741 BracketBatch0171.bracket2742
  (1707542155591068988849608726717458460538257/20000000000000000000000000000000000000000) (1173831939133080036561857522404355032423/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2741
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2742
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (213624463813377955108113451289006372610209/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (213624463813377955108113451289006372610209/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (171191275924150762984486273304540435037423/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (171191275924150762984486273304540435037423/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (1710454234874265635354885171678727665627951/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1710454234874265635354885171678727665627951/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2742 BracketBatch0171.bracket2743 (1710454234874265635354885171678727665627951/20000000000000000000000000000000000000000) (234870909856299096852108501611172988647/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2742 BracketBatch0171.bracket2743
  (1710454234874265635354885171678727665627951/20000000000000000000000000000000000000000) (234870909856299096852108501611172988647/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2742
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2743
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (106994547452594226865303920815337771898389/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (106994547452594226865303920815337771898389/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (857419898967285082191204738940857721938849/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (857419898967285082191204738940857721938849/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (1713376278588038897113636105463559897125961/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1713376278588038897113636105463559897125961/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0342.rows ScalarLogs0342.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2743 BracketBatch0171.bracket2744 (1713376278588038897113636105463559897125961/20000000000000000000000000000000000000000) (2937195185933594805813684475200731369839/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2743 BracketBatch0171.bracket2744
  (1713376278588038897113636105463559897125961/20000000000000000000000000000000000000000) (2937195185933594805813684475200731369839/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2743
