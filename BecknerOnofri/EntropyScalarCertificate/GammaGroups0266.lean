module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0332
public import BecknerOnofri.EntropyScalarCertificate.Bessel0333
public import BecknerOnofri.EntropyScalarCertificate.Bessel0655
public import BecknerOnofri.EntropyScalarCertificate.Brackets0133
public import BecknerOnofri.EntropyScalarCertificate.Logs0266
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2128
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (72750847948989024708405510079359678640141/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (72750847948989024708405510079359678640141/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (72955285688669533607187672440837301741539/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (72955285688669533607187672440837301741539/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (1821326670470731978944914781502462254771/250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1821326670470731978944914781502462254771/250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2128 BracketBatch0133.bracket2129 (1821326670470731978944914781502462254771/250000000000000000000000000000000000000) (469502705033229150754100013845337454277/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2128 BracketBatch0133.bracket2129
  (1821326670470731978944914781502462254771/250000000000000000000000000000000000000) (469502705033229150754100013845337454277/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2128
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2129
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (2279852677770922925224614763776165679423/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2279852677770922925224614763776165679423/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (14632179964383892480075462951903251123549/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14632179964383892480075462951903251123549/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (146116185510588996007564987200353557359281/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (146116185510588996007564987200353557359281/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2129 BracketBatch0133.bracket2130 (146116185510588996007564987200353557359281/20000000000000000000000000000000000000000) (2351145255851262597707744336713296080407/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2129 BracketBatch0133.bracket2130
  (146116185510588996007564987200353557359281/20000000000000000000000000000000000000000) (2351145255851262597707744336713296080407/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2129
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2130
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (36580449910959731200188657379758127808871/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (36580449910959731200188657379758127808871/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (36683850258869096513398915043403113138269/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (36683850258869096513398915043403113138269/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (3663215008491441385679378621158062047357/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3663215008491441385679378621158062047357/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2130 BracketBatch0133.bracket2131 (3663215008491441385679378621158062047357/500000000000000000000000000000000000000) (1177394215785018365925804074609956646069/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2130 BracketBatch0133.bracket2131
  (3663215008491441385679378621158062047357/500000000000000000000000000000000000000) (1177394215785018365925804074609956646069/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2130
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2131
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0332.rows BesselBatch0332.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (14673540103547638605359566017361245255307/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14673540103547638605359566017361245255307/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (3678784903134482341124687157914111759443/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3678784903134482341124687157914111759443/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (29388679716085567969858314649017692293079/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (29388679716085567969858314649017692293079/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2131 BracketBatch0133.bracket2132 (29388679716085567969858314649017692293079/4000000000000000000000000000000000000000) (1179221559900653477989213798803238934571/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2131 BracketBatch0133.bracket2132
  (29388679716085567969858314649017692293079/4000000000000000000000000000000000000000) (1179221559900653477989213798803238934571/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2131
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2132
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (73575698062689646822493743158282235188857/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (73575698062689646822493743158282235188857/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (73784902862606098780909493816702023107399/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (73784902862606098780909493816702023107399/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (2302509389457746025053175577734129035879/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2302509389457746025053175577734129035879/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2132 BracketBatch0133.bracket2133 (2302509389457746025053175577734129035879/312500000000000000000000000000000000000) (2362109388616856409716598575087877809421/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2132 BracketBatch0133.bracket2133
  (2302509389457746025053175577734129035879/312500000000000000000000000000000000000) (2362109388616856409716598575087877809421/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2132
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2133
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (18446225715651524695227373454175505776849/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18446225715651524695227373454175505776849/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1479906508886434193673767506734672553843/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1479906508886434193673767506734672553843/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (73890114153463904232298934576717825399773/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (73890114153463904232298934576717825399773/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2133 BracketBatch0133.bracket2134 (73890114153463904232298934576717825399773/10000000000000000000000000000000000000000) (2365787306688214421072784840065101888439/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2133 BracketBatch0133.bracket2134
  (73890114153463904232298934576717825399773/10000000000000000000000000000000000000000) (2365787306688214421072784840065101888439/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2133
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2134
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (73995325444321709683688375336733627692147/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (73995325444321709683688375336733627692147/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (74206976457436382587196036592836199090713/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (74206976457436382587196036592836199090713/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (7410115095087904613544220596478491339143/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7410115095087904613544220596478491339143/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2134 BracketBatch0133.bracket2135 (7410115095087904613544220596478491339143/1000000000000000000000000000000000000000) (592369235823388593111691281375673488129/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2134 BracketBatch0133.bracket2135
  (7410115095087904613544220596478491339143/1000000000000000000000000000000000000000) (592369235823388593111691281375673488129/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2134
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2135
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (7420697645743638258719603659283619909071/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7420697645743638258719603659283619909071/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0333.rows BesselBatch0333.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (4651241667256910271041557951532686284741/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4651241667256910271041557951532686284741/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0655.rows BesselBatch0655.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (74313421566773473461930481908679589823283/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (74313421566773473461930481908679589823283/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0266.rows ScalarLogs0266.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0133.bracket2135 BracketBatch0133.bracket2136 (74313421566773473461930481908679589823283/10000000000000000000000000000000000000000) (593294592081172297081634025469544768503/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0133.bracket2135 BracketBatch0133.bracket2136
  (74313421566773473461930481908679589823283/10000000000000000000000000000000000000000) (593294592081172297081634025469544768503/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2135
