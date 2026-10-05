import BecknerOnofri.EntropyScalarCertificate.Bessel0352
import BecknerOnofri.EntropyScalarCertificate.Bessel0353
import BecknerOnofri.EntropyScalarCertificate.Bessel0665
import BecknerOnofri.EntropyScalarCertificate.Brackets0141
import BecknerOnofri.EntropyScalarCertificate.Logs0282
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2256
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (113906761705114372608668684601348299806351/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (113906761705114372608668684601348299806351/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (22883221953949400795877113686956359774473/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22883221953949400795877113686956359774473/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (57080717868715344147013563259032524669679/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (57080717868715344147013563259032524669679/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2256 BracketBatch0141.bracket2257 (57080717868715344147013563259032524669679/5000000000000000000000000000000000000000) (2936831449625549022754026675003460898831/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2256 BracketBatch0141.bracket2257
  (57080717868715344147013563259032524669679/5000000000000000000000000000000000000000) (2936831449625549022754026675003460898831/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2256
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2257
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (57208054884873501989692784217390899436181/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (57208054884873501989692784217390899436181/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (57465045157602636772557690725316007231111/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (57465045157602636772557690725316007231111/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (28668275010619034690562618735676726666823/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28668275010619034690562618735676726666823/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2257 BracketBatch0141.bracket2258 (28668275010619034690562618735676726666823/2500000000000000000000000000000000000000) (588554973257832534459888191802297936387/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2257 BracketBatch0141.bracket2258
  (28668275010619034690562618735676726666823/2500000000000000000000000000000000000000) (588554973257832534459888191802297936387/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2257
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2258
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (114930090315205273545115381450632014462219/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (114930090315205273545115381450632014462219/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (28862191699567637773139017426856207987451/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (28862191699567637773139017426856207987451/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (230378857113475824637671451158056846412023/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (230378857113475824637671451158056846412023/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2258 BracketBatch0141.bracket2259 (230378857113475824637671451158056846412023/20000000000000000000000000000000000000000) (737186713537950489714112352286683632093/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2258 BracketBatch0141.bracket2259
  (230378857113475824637671451158056846412023/20000000000000000000000000000000000000000) (737186713537950489714112352286683632093/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2258
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2259
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0352.rows BesselBatch0352.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (115448766798270551092556069707424831949801/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (115448766798270551092556069707424831949801/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (115972203840072424354441011520984723950991/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (115972203840072424354441011520984723950991/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (28927621329792871930874635153551194487599/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28927621329792871930874635153551194487599/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2259 BracketBatch0141.bracket2260 (28927621329792871930874635153551194487599/2500000000000000000000000000000000000000) (1477373832770127463061692823546589419869/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2259 BracketBatch0141.bracket2260
  (28927621329792871930874635153551194487599/2500000000000000000000000000000000000000) (1477373832770127463061692823546589419869/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2259
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2260
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (28993050960018106088610252880246180987747/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (28993050960018106088610252880246180987747/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (116500467252916986467328372809962442112149/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (116500467252916986467328372809962442112149/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (232472671092989410821769384330947166063137/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (232472671092989410821769384330947166063137/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2260 BracketBatch0141.bracket2261 (232472671092989410821769384330947166063137/20000000000000000000000000000000000000000) (1480388777945674636450559329913581658267/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2260 BracketBatch0141.bracket2261
  (232472671092989410821769384330947166063137/20000000000000000000000000000000000000000) (1480388777945674636450559329913581658267/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2260
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2261
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (58250233626458493233664186404981221056073/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (58250233626458493233664186404981221056073/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (58516812033930176852857595011085576737817/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (58516812033930176852857595011085576737817/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (11676704566038867008652178141606679779389/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11676704566038867008652178141606679779389/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2261 BracketBatch0141.bracket2262 (11676704566038867008652178141606679779389/1000000000000000000000000000000000000000) (148341839189874726019322329214024402237/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2261 BracketBatch0141.bracket2262
  (11676704566038867008652178141606679779389/1000000000000000000000000000000000000000) (148341839189874726019322329214024402237/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2261
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2262
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (117033624067860353705715190022171153475631/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (117033624067860353705715190022171153475631/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (117571742563051676803223539338218705256757/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (117571742563051676803223539338218705256757/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (58651341657728007627234682340097464683097/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (58651341657728007627234682340097464683097/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2262 BracketBatch0141.bracket2263 (58651341657728007627234682340097464683097/5000000000000000000000000000000000000000) (594585122210574703475888192371133459403/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2262 BracketBatch0141.bracket2263
  (58651341657728007627234682340097464683097/5000000000000000000000000000000000000000) (594585122210574703475888192371133459403/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2262
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2263
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (58785871281525838401611769669109352628377/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (58785871281525838401611769669109352628377/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0353.rows BesselBatch0353.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (118114892292870816211267260372196665104553/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (118114892292870816211267260372196665104553/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0665.rows BesselBatch0665.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (235686634855922493014490799710415370361307/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (235686634855922493014490799710415370361307/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0282.rows ScalarLogs0282.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0141.bracket2263 BracketBatch0141.bracket2264 (235686634855922493014490799710415370361307/20000000000000000000000000000000000000000) (2979044302700285799799947058483346230361/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0141.bracket2263 BracketBatch0141.bracket2264
  (235686634855922493014490799710415370361307/20000000000000000000000000000000000000000) (2979044302700285799799947058483346230361/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2263
