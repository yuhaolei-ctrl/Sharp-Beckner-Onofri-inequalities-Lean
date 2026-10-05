module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0392
public import BecknerOnofri.EntropyScalarCertificate.Bessel0393
public import BecknerOnofri.EntropyScalarCertificate.Bessel0685
public import BecknerOnofri.EntropyScalarCertificate.Brackets0157
public import BecknerOnofri.EntropyScalarCertificate.Logs0314
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2512
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (342794037872122782186197037460972632535851/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (342794037872122782186197037460972632535851/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (21483106107681698260687706768799919387727/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21483106107681698260687706768799919387727/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (686523735595029954357200345761771342739483/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (686523735595029954357200345761771342739483/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2512 BracketBatch0157.bracket2513 (686523735595029954357200345761771342739483/20000000000000000000000000000000000000000) (1122848671050738326081744353423847716057/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2512 BracketBatch0157.bracket2513
  (686523735595029954357200345761771342739483/20000000000000000000000000000000000000000) (1122848671050738326081744353423847716057/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2512
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2513
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (343729697722907172171003308300798710203629/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (343729697722907172171003308300798710203629/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (344670498779856152002526474257947862869203/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (344670498779856152002526474257947862869203/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (10756253070355676940211402852480415204263/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10756253070355676940211402852480415204263/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2513 BracketBatch0157.bracket2514 (10756253070355676940211402852480415204263/312500000000000000000000000000000000000) (4495364356690775248986319748702226845603/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2513 BracketBatch0157.bracket2514
  (10756253070355676940211402852480415204263/312500000000000000000000000000000000000) (4495364356690775248986319748702226845603/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2513
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2514
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (861676246949640380006316185644869657173/25000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (861676246949640380006316185644869657173/25000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (345616483532242201522299310551246118415503/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (345616483532242201522299310551246118415503/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (690286982312098353524825784809193981284703/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (690286982312098353524825784809193981284703/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2514 BracketBatch0157.bracket2515 (690286982312098353524825784809193981284703/20000000000000000000000000000000000000000) (4499345552092120053300374789450536751249/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2514 BracketBatch0157.bracket2515
  (690286982312098353524825784809193981284703/20000000000000000000000000000000000000000) (4499345552092120053300374789450536751249/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2514
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2515
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0392.rows BesselBatch0392.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (691232967064484403044598621102492236831/20000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (691232967064484403044598621102492236831/20000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (17328384746941626760354147179291061045743/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17328384746941626760354147179291061045743/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (17304604461776868418234556353426683483259/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17304604461776868418234556353426683483259/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2515 BracketBatch0157.bracket2516 (17304604461776868418234556353426683483259/500000000000000000000000000000000000000) (4503338332169731063535006043612926928071/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2515 BracketBatch0157.bracket2516
  (17304604461776868418234556353426683483259/500000000000000000000000000000000000000) (4503338332169731063535006043612926928071/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2515
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2516
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (346567694938832535207082943585821220914857/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (346567694938832535207082943585821220914857/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (347524176434391799318455565977463217294299/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (347524176434391799318455565977463217294299/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (173522967843306083631384627390821109552289/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (173522967843306083631384627390821109552289/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2516 BracketBatch0157.bracket2517 (173522967843306083631384627390821109552289/5000000000000000000000000000000000000000) (4507342759169054768849084986601726120411/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2516 BracketBatch0157.bracket2517
  (173522967843306083631384627390821109552289/5000000000000000000000000000000000000000) (4507342759169054768849084986601726120411/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2516
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2517
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (43440522054298974914806945747182902161787/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (43440522054298974914806945747182902161787/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (5445093311504580427159883682300626572697/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5445093311504580427159883682300626572697/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (87001268546335618332086015205587914743363/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (87001268546335618332086015205587914743363/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2517 BracketBatch0157.bracket2518 (87001268546335618332086015205587914743363/2500000000000000000000000000000000000000) (2255679447911553561229823306433296356623/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2517 BracketBatch0157.bracket2518
  (87001268546335618332086015205587914743363/2500000000000000000000000000000000000000) (2255679447911553561229823306433296356623/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2517
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2518
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (69697194387258629467646511133448020130521/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (69697194387258629467646511133448020130521/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (34945312585123980691534701809111189212881/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (34945312585123980691534701809111189212881/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (139587819557506590850715914751670398556283/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (139587819557506590850715914751670398556283/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2518 BracketBatch0157.bracket2519 (139587819557506590850715914751670398556283/4000000000000000000000000000000000000000) (2257693402678699121547303822846745287067/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2518 BracketBatch0157.bracket2519
  (139587819557506590850715914751670398556283/4000000000000000000000000000000000000000) (2257693402678699121547303822846745287067/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2518
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2519
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (349453125851239806915347018091111892128807/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (349453125851239806915347018091111892128807/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (87606420770524824693184713650127595360889/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (87606420770524824693184713650127595360889/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (699878808933339105688085872691622273572363/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (699878808933339105688085872691622273572363/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0314.rows ScalarLogs0314.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2519 BracketBatch0157.bracket2520 (699878808933339105688085872691622273572363/20000000000000000000000000000000000000000) (451942655149491627129142185521927979449/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2519 BracketBatch0157.bracket2520
  (699878808933339105688085872691622273572363/20000000000000000000000000000000000000000) (451942655149491627129142185521927979449/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2519
