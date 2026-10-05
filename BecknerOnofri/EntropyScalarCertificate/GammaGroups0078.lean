import BecknerOnofri.EntropyScalarCertificate.Bessel0097
import BecknerOnofri.EntropyScalarCertificate.Bessel0098
import BecknerOnofri.EntropyScalarCertificate.Bessel0537
import BecknerOnofri.EntropyScalarCertificate.Bessel0538
import BecknerOnofri.EntropyScalarCertificate.Brackets0039
import BecknerOnofri.EntropyScalarCertificate.Logs0078
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0624
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (921819447251399412626622315719632305373/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (921819447251399412626622315719632305373/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (369148466054050813661081692225178642609/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (369148466054050813661081692225178642609/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (3689381224773052893558653092565157823791/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3689381224773052893558653092565157823791/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0624 BracketBatch0039.bracket0625 (3689381224773052893558653092565157823791/20000000000000000000000000000000000000000) (426288793830928678700036848878411869/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0624 BracketBatch0039.bracket0625
  (3689381224773052893558653092565157823791/20000000000000000000000000000000000000000) (426288793830928678700036848878411869/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0624
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0625
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (922871165135127034152704230562946606521/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (922871165135127034152704230562946606521/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1847846005155860515111623947063417244003/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1847846005155860515111623947063417244003/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (738717667085222916683406481637862091409/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (738717667085222916683406481637862091409/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0625 BracketBatch0039.bracket0626 (738717667085222916683406481637862091409/4000000000000000000000000000000000000000) (428186621988144265283661041557559883/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0625 BracketBatch0039.bracket0626
  (738717667085222916683406481637862091409/4000000000000000000000000000000000000000) (428186621988144265283661041557559883/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0625
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0626
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (461961501288965128777905986765854311/2500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (461961501288965128777905986765854311/2500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (924974959736711498858178534732979633927/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (924974959736711498858178534732979633927/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (1848897962314641756413990508264688255927/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1848897962314641756413990508264688255927/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0626 BracketBatch0039.bracket0627 (1848897962314641756413990508264688255927/10000000000000000000000000000000000000000) (860181640076939040158929070053686183/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0626 BracketBatch0039.bracket0627
  (1848897962314641756413990508264688255927/10000000000000000000000000000000000000000) (860181640076939040158929070053686183/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0626
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0627
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0097.rows BesselBatch0097.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1849949919473422997716357069465959267851/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1849949919473422997716357069465959267851/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (1852054073536927794677768111587169292507/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1852054073536927794677768111587169292507/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (1851001996505175396197062590526564280179/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1851001996505175396197062590526564280179/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0627 BracketBatch0039.bracket0628 (1851001996505175396197062590526564280179/10000000000000000000000000000000000000000) (86400280502041323044810755468861309/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0627 BracketBatch0039.bracket0628
  (1851001996505175396197062590526564280179/10000000000000000000000000000000000000000) (86400280502041323044810755468861309/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0627
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0628
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (231506759192115974334721013948396161563/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (231506759192115974334721013948396161563/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (927079233830271460229762940602492753417/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (927079233830271460229762940602492753417/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0537.rows BesselBatch0537.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (1853106270598735357568646996396077399669/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1853106270598735357568646996396077399669/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0628 BracketBatch0039.bracket0629 (1853106270598735357568646996396077399669/10000000000000000000000000000000000000000) (216959191974931344705556958222317853/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0628 BracketBatch0039.bracket0629
  (1853106270598735357568646996396077399669/10000000000000000000000000000000000000000) (216959191974931344705556958222317853/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0628
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0629
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (1854158467660542920459525881204985506831/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1854158467660542920459525881204985506831/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1856263102158618415167248945086690630297/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1856263102158618415167248945086690630297/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (463802696227395166953346853286459517141/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (463802696227395166953346853286459517141/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0629 BracketBatch0039.bracket0630 (463802696227395166953346853286459517141/2500000000000000000000000000000000000000) (871683557844315355462705726849385967/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0629 BracketBatch0039.bracket0630
  (463802696227395166953346853286459517141/2500000000000000000000000000000000000000) (871683557844315355462705726849385967/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0629
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0630
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (928131551079309207583624472543345315147/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (928131551079309207583624472543345315147/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (185836797734568663463025019478910852597/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (185836797734568663463025019478910852597/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (464328884938038131224687392484474894533/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (464328884938038131224687392484474894533/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0630 BracketBatch0039.bracket0631 (464328884938038131224687392484474894533/2500000000000000000000000000000000000000) (437771602010032153368838635249331877/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0630 BracketBatch0039.bracket0631
  (464328884938038131224687392484474894533/2500000000000000000000000000000000000000) (437771602010032153368838635249331877/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0630
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0631
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1858367977345686634630250194789108525967/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1858367977345686634630250194789108525967/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0098.rows BesselBatch0098.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1860473093536462540829262291899287434527/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1860473093536462540829262291899287434527/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0538.rows BesselBatch0538.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (1859420535441074587729756243344197980247/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1859420535441074587729756243344197980247/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0078.rows ScalarLogs0078.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0039.bracket0631 BracketBatch0039.bracket0632 (1859420535441074587729756243344197980247/10000000000000000000000000000000000000000) (879415735629310362332435676679630841/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0039.bracket0631 BracketBatch0039.bracket0632
  (1859420535441074587729756243344197980247/10000000000000000000000000000000000000000) (879415735629310362332435676679630841/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0631
