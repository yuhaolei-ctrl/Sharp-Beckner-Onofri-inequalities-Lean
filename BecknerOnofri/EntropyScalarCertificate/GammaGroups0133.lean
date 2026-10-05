module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0166
public import BecknerOnofri.EntropyScalarCertificate.Bessel0167
public import BecknerOnofri.EntropyScalarCertificate.Bessel0572
public import BecknerOnofri.EntropyScalarCertificate.Brackets0066
public import BecknerOnofri.EntropyScalarCertificate.Brackets0067
public import BecknerOnofri.EntropyScalarCertificate.Logs0133
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1064
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (3279045008283678399694186032671026135641/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3279045008283678399694186032671026135641/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (263024783385147373252558762962205266141/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (263024783385147373252558762962205266141/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (13133709601196041130702341139397183924807/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13133709601196041130702341139397183924807/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1064 BracketBatch0066.bracket1065 (13133709601196041130702341139397183924807/20000000000000000000000000000000000000000) (39812797603324198944801223876484671429/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1064 BracketBatch0066.bracket1065
  (13133709601196041130702341139397183924807/20000000000000000000000000000000000000000) (39812797603324198944801223876484671429/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1064
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1065
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (3287809792314342165656984537027565826761/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3287809792314342165656984537027565826761/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (824149375577054397978244732737250803509/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (824149375577054397978244732737250803509/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (6584407294622559757569963467976569040797/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6584407294622559757569963467976569040797/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1065 BracketBatch0066.bracket1066 (6584407294622559757569963467976569040797/10000000000000000000000000000000000000000) (40130393662501107095727617204120415139/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1065 BracketBatch0066.bracket1066
  (6584407294622559757569963467976569040797/10000000000000000000000000000000000000000) (40130393662501107095727617204120415139/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1065
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1066
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (6593195004616435183825957861898006428069/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6593195004616435183825957861898006428069/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (1652704144253186064265305261167886119139/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1652704144253186064265305261167886119139/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (105632092653033435527097431252556407237/160000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (105632092653033435527097431252556407237/160000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1066 BracketBatch0066.bracket1067 (105632092653033435527097431252556407237/160000000000000000000000000000000000000) (80900145588994936483657432345990904817/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1066 BracketBatch0066.bracket1067
  (105632092653033435527097431252556407237/160000000000000000000000000000000000000) (80900145588994936483657432345990904817/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1066
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1067
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (6610816577012744257061221044671544476553/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6610816577012744257061221044671544476553/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1325696920987195819892721687302926728079/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1325696920987195819892721687302926728079/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (3309825295487180839131207370296544529237/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3309825295487180839131207370296544529237/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1067 BracketBatch0066.bracket1068 (3309825295487180839131207370296544529237/5000000000000000000000000000000000000000) (509648085946909406851427240436049871/62500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1067 BracketBatch0066.bracket1068
  (3309825295487180839131207370296544529237/5000000000000000000000000000000000000000) (509648085946909406851427240436049871/62500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1067
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1068
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0166.rows BesselBatch0166.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (828560575616997387432951054564329205049/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (828560575616997387432951054564329205049/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (6646199394171171530468822675251162241807/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6646199394171171530468822675251162241807/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (13274683999107150629932431111765795882199/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13274683999107150629932431111765795882199/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1068 BracketBatch0066.bracket1069 (13274683999107150629932431111765795882199/20000000000000000000000000000000000000000) (82191455715670387257428725341332038539/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1068 BracketBatch0066.bracket1069
  (13274683999107150629932431111765795882199/20000000000000000000000000000000000000000) (82191455715670387257428725341332038539/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1068
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1069
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1661549848542792882617205668812790560451/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1661549848542792882617205668812790560451/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (3331980626600437982819075647795297097717/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3331980626600437982819075647795297097717/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (6655080323686023748053486985420878218619/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6655080323686023748053486985420878218619/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1069 BracketBatch0066.bracket1070 (6655080323686023748053486985420878218619/10000000000000000000000000000000000000000) (1294428992755025032750108958265933057/156250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1069 BracketBatch0066.bracket1070
  (6655080323686023748053486985420878218619/10000000000000000000000000000000000000000) (1294428992755025032750108958265933057/156250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1069
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1070
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (6663961253200875965638151295590594195431/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6663961253200875965638151295590594195431/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (417610655827278842762703427201037263009/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (417610655827278842762703427201037263009/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (533829269857493497993656245232287616143/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (533829269857493497993656245232287616143/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1070 BracketBatch0066.bracket1071 (533829269857493497993656245232287616143/800000000000000000000000000000000000000) (83499717421444090906586512536140167663/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1070 BracketBatch0066.bracket1071
  (533829269857493497993656245232287616143/800000000000000000000000000000000000000) (83499717421444090906586512536140167663/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1070
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1071
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (6681770493236461484203254835216596208141/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6681770493236461484203254835216596208141/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0167.rows BesselBatch0167.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1674906857062461202995384251149318081329/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1674906857062461202995384251149318081329/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0572.rows BesselBatch0572.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (13381397921486306296184791839813868533457/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13381397921486306296184791839813868533457/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0133.rows ScalarLogs0133.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0066.bracket1071 BracketBatch0067.bracket1072 (13381397921486306296184791839813868533457/20000000000000000000000000000000000000000) (1315004152088324153881999604210611537/156250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0066.bracket1071 BracketBatch0067.bracket1072
  (13381397921486306296184791839813868533457/20000000000000000000000000000000000000000) (1315004152088324153881999604210611537/156250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1071
