import BecknerOnofri.EntropyScalarCertificate.Bessel0327
import BecknerOnofri.EntropyScalarCertificate.Bessel0328
import BecknerOnofri.EntropyScalarCertificate.Bessel0652
import BecknerOnofri.EntropyScalarCertificate.Bessel0653
import BecknerOnofri.EntropyScalarCertificate.Brackets0131
import BecknerOnofri.EntropyScalarCertificate.Logs0262
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2096
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (33387350180782075668067182276044011293269/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (33387350180782075668067182276044011293269/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (2677849539683692658971748278823678143647/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2677849539683692658971748278823678143647/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (133720938853656467810428071522679976177713/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (133720938853656467810428071522679976177713/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2096 BracketBatch0131.bracket2097 (133720938853656467810428071522679976177713/20000000000000000000000000000000000000000) (279620751833616567526506735716765452201/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2096 BracketBatch0131.bracket2097
  (133720938853656467810428071522679976177713/20000000000000000000000000000000000000000) (279620751833616567526506735716765452201/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2096
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2097
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (16736559623023079118573426742647988397793/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16736559623023079118573426742647988397793/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (67118680842897645873686020331573755774283/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (67118680842897645873686020331573755774283/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (26812983866997992469595945460433141873091/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (26812983866997992469595945460433141873091/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2097 BracketBatch0131.bracket2098 (26812983866997992469595945460433141873091/4000000000000000000000000000000000000000) (448052781649931162896681121421415073779/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2097 BracketBatch0131.bracket2098
  (26812983866997992469595945460433141873091/4000000000000000000000000000000000000000) (448052781649931162896681121421415073779/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2097
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2098
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (1677967021072441146842150508289343894357/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1677967021072441146842150508289343894357/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (16823008642463546583946845791952933483223/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16823008642463546583946845791952933483223/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (33602678853187958052368350874846372426793/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33602678853187958052368350874846372426793/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2098 BracketBatch0131.bracket2099 (33602678853187958052368350874846372426793/5000000000000000000000000000000000000000) (1121785682200167321765478388016433128823/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2098 BracketBatch0131.bracket2099
  (33602678853187958052368350874846372426793/5000000000000000000000000000000000000000) (1121785682200167321765478388016433128823/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2098
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2099
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0327.rows BesselBatch0327.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (67292034569854186335787383167811733932889/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (67292034569854186335787383167811733932889/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (33733153452281858779386523595730250908471/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (33733153452281858779386523595730250908471/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (134758341474417903894560430359272235749831/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (134758341474417903894560430359272235749831/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2099 BracketBatch0131.bracket2100 (134758341474417903894560430359272235749831/20000000000000000000000000000000000000000) (449377686943229818937969204634228840081/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2099 BracketBatch0131.bracket2100
  (134758341474417903894560430359272235749831/20000000000000000000000000000000000000000) (449377686943229818937969204634228840081/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2099
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2100
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (67466306904563717558773047191460501816939/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (67466306904563717558773047191460501816939/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (67641505155360074530794052704389837273213/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (67641505155360074530794052704389837273213/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0652.rows BesselBatch0652.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (16888476507490474011195887486981292386269/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16888476507490474011195887486981292386269/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2100 BracketBatch0131.bracket2101 (16888476507490474011195887486981292386269/2500000000000000000000000000000000000000) (2250215171210056479262164683436525850687/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2100 BracketBatch0131.bracket2101
  (16888476507490474011195887486981292386269/2500000000000000000000000000000000000000) (2250215171210056479262164683436525850687/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2100
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2101
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (6764150515536007453079405270438983727321/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6764150515536007453079405270438983727321/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (13563527341665899313083540110481019532849/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13563527341665899313083540110481019532849/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (27091828372737914219242350651358986987491/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (27091828372737914219242350651358986987491/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2101 BracketBatch0131.bracket2102 (27091828372737914219242350651358986987491/4000000000000000000000000000000000000000) (281693953289651625919239750231354555389/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2101 BracketBatch0131.bracket2102
  (27091828372737914219242350651358986987491/4000000000000000000000000000000000000000) (281693953289651625919239750231354555389/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2101
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2102
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (33908818354164748282708850276202548832121/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (33908818354164748282708850276202548832121/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (13598941805669460428354479453716391636917/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13598941805669460428354479453716391636917/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (135812345736676798707190097820987055848827/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (135812345736676798707190097820987055848827/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2102 BracketBatch0131.bracket2103 (135812345736676798707190097820987055848827/20000000000000000000000000000000000000000) (2256897852899453109318410736378250069591/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2102 BracketBatch0131.bracket2103
  (135812345736676798707190097820987055848827/20000000000000000000000000000000000000000) (2256897852899453109318410736378250069591/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2102
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2103
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (33997354514173651070886198634290979092291/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (33997354514173651070886198634290979092291/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0328.rows BesselBatch0328.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (68172729660131195111101203016098000366581/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (68172729660131195111101203016098000366581/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (136167438688478497252873600284679958551163/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (136167438688478497252873600284679958551163/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0262.rows ScalarLogs0262.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0131.bracket2103 BracketBatch0131.bracket2104 (136167438688478497252873600284679958551163/20000000000000000000000000000000000000000) (2260253904249827316303327820704241241739/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0131.bracket2103 BracketBatch0131.bracket2104
  (136167438688478497252873600284679958551163/20000000000000000000000000000000000000000) (2260253904249827316303327820704241241739/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2103
