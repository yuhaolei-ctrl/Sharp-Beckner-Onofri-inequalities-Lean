import BecknerOnofri.EntropyScalarCertificate.Bessel0117
import BecknerOnofri.EntropyScalarCertificate.Bessel0118
import BecknerOnofri.EntropyScalarCertificate.Bessel0547
import BecknerOnofri.EntropyScalarCertificate.Bessel0548
import BecknerOnofri.EntropyScalarCertificate.Brackets0047
import BecknerOnofri.EntropyScalarCertificate.Logs0094
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0752
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (481429740569412059688952847960599528591/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (481429740569412059688952847960599528591/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (2418041515755731248905339557162332761709/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2418041515755731248905339557162332761709/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (603148777325348943418762974620666300583/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (603148777325348943418762974620666300583/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0752 BracketBatch0047.bracket0753 (603148777325348943418762974620666300583/2500000000000000000000000000000000000000) (2375865745354769283043088053897520011/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0752 BracketBatch0047.bracket0753
  (603148777325348943418762974620666300583/2500000000000000000000000000000000000000) (2375865745354769283043088053897520011/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0752
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0753
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1209020757877865624452669778581166380853/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1209020757877865624452669778581166380853/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (19431540733695662702299884314489734647/80000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19431540733695662702299884314489734647/80000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (4846984107467689086692825096473549592581/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4846984107467689086692825096473549592581/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0753 BracketBatch0047.bracket0754 (4846984107467689086692825096473549592581/20000000000000000000000000000000000000000) (2417402499029750186392607058476600349/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0753 BracketBatch0047.bracket0754
  (4846984107467689086692825096473549592581/20000000000000000000000000000000000000000) (2417402499029750186392607058476600349/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0753
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0754
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (303617823963994729723435692413902103859/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (303617823963994729723435692413902103859/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (2439851977521868485984252598638797610853/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2439851977521868485984252598638797610853/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (194751782769353052950869525518000577669/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (194751782769353052950869525518000577669/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0754 BracketBatch0047.bracket0755 (194751782769353052950869525518000577669/800000000000000000000000000000000000000) (2459485554684781284372386434172952599/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0754 BracketBatch0047.bracket0755
  (194751782769353052950869525518000577669/800000000000000000000000000000000000000) (2459485554684781284372386434172952599/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0754
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0755
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0117.rows BesselBatch0117.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (48797039550437369719685051972775952217/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (48797039550437369719685051972775952217/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (2450769720163601495184200894260721607901/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2450769720163601495184200894260721607901/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (4890621697685469981168453492899519218751/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4890621697685469981168453492899519218751/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0755 BracketBatch0047.bracket0756 (4890621697685469981168453492899519218751/20000000000000000000000000000000000000000) (2502119849510373498727878004383534193/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0755 BracketBatch0047.bracket0756
  (4890621697685469981168453492899519218751/20000000000000000000000000000000000000000) (2502119849510373498727878004383534193/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0755
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0756
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1225384860081800747592100447130360803949/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1225384860081800747592100447130360803949/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (492339173357719617309060760095740379937/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (492339173357719617309060760095740379937/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0547.rows BesselBatch0547.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (4912465586952199581729504694739423507583/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4912465586952199581729504694739423507583/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0756 BracketBatch0047.bracket0757 (4912465586952199581729504694739423507583/20000000000000000000000000000000000000000) (2545310346695444634876369383036841297/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0756 BracketBatch0047.bracket0757
  (4912465586952199581729504694739423507583/20000000000000000000000000000000000000000) (2545310346695444634876369383036841297/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0756
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0757
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (1230847933394299043272651900239350949841/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1230847933394299043272651900239350949841/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (494526092944580930229454356637014699319/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (494526092944580930229454356637014699319/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (4934326331511502737692575583663775396277/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4934326331511502737692575583663775396277/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0757 BracketBatch0047.bracket0758 (4934326331511502737692575583663775396277/20000000000000000000000000000000000000000) (323632754437488934232045585884668421/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0757 BracketBatch0047.bracket0758
  (4934326331511502737692575583663775396277/20000000000000000000000000000000000000000) (323632754437488934232045585884668421/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0757
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0758
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (154539404045181540696704486449067093537/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (154539404045181540696704486449067093537/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (2483573561468484302932878194741130412939/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2483573561468484302932878194741130412939/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (4956204026191388954080149977926203909531/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4956204026191388954080149977926203909531/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0758 BracketBatch0047.bracket0759 (4956204026191388954080149977926203909531/20000000000000000000000000000000000000000) (658344982831948532501657666724960569/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0758 BracketBatch0047.bracket0759
  (4956204026191388954080149977926203909531/20000000000000000000000000000000000000000) (658344982831948532501657666724960569/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0758
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0759
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (310446695183560537866609774342641301617/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (310446695183560537866609774342641301617/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0118.rows BesselBatch0118.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (2494525204704537825793310289986172008101/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2494525204704537825793310289986172008101/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0548.rows BesselBatch0548.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (4978098766173022128726188484727302421037/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4978098766173022128726188484727302421037/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0094.rows ScalarLogs0094.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0047.bracket0759 BracketBatch0047.bracket0760 (4978098766173022128726188484727302421037/20000000000000000000000000000000000000000) (1339134537900418022562242378027736663/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0047.bracket0759 BracketBatch0047.bracket0760
  (4978098766173022128726188484727302421037/20000000000000000000000000000000000000000) (1339134537900418022562242378027736663/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0759
