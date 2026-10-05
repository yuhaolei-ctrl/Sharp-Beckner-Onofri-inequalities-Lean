import BecknerOnofri.EntropyScalarCertificate.Bessel0433
import BecknerOnofri.EntropyScalarCertificate.Bessel0434
import BecknerOnofri.EntropyScalarCertificate.Bessel0435
import BecknerOnofri.EntropyScalarCertificate.Bessel0705
import BecknerOnofri.EntropyScalarCertificate.Bessel0706
import BecknerOnofri.EntropyScalarCertificate.Brackets0173
import BecknerOnofri.EntropyScalarCertificate.Brackets0174
import BecknerOnofri.EntropyScalarCertificate.Logs0347
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2776
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (181410462505293945192118517531273203592697/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (181410462505293945192118517531273203592697/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (14198378404763437813264543384342201396551/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14198378404763437813264543384342201396551/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (1815748530431329746009523364254266907342749/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1815748530431329746009523364254266907342749/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2776 BracketBatch0173.bracket2777 (1815748530431329746009523364254266907342749/20000000000000000000000000000000000000000) (1192688556876787944399579326861082334029/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2776 BracketBatch0173.bracket2777
  (1815748530431329746009523364254266907342749/20000000000000000000000000000000000000000) (1192688556876787944399579326861082334029/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2776
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2777
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0433.rows BesselBatch0433.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (908696217904860020048930776597900889379261/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (908696217904860020048930776597900889379261/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (455173050577899961031304433355914170337703/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (455173050577899961031304433355914170337703/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (1819042319060659942111539643309729230054667/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1819042319060659942111539643309729230054667/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2777 BracketBatch0173.bracket2778 (1819042319060659942111539643309729230054667/20000000000000000000000000000000000000000) (5966225583451456313335435014226878370537/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2777 BracketBatch0173.bracket2778
  (1819042319060659942111539643309729230054667/20000000000000000000000000000000000000000) (5966225583451456313335435014226878370537/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2777
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2778
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (910346101155799922062608866711828340675403/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (910346101155799922062608866711828340675403/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (912001994945258313694821100280493394348191/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (912001994945258313694821100280493394348191/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0705.rows BesselBatch0705.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (911174048050529117878714983496160867511797/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (911174048050529117878714983496160867511797/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2778 BracketBatch0173.bracket2779 (911174048050529117878714983496160867511797/10000000000000000000000000000000000000000) (1492253385383945088384033542942021280719/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2778 BracketBatch0173.bracket2779
  (911174048050529117878714983496160867511797/10000000000000000000000000000000000000000) (1492253385383945088384033542942021280719/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2778
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2779
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (228000498736314578423705275070123348587047/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (228000498736314578423705275070123348587047/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (114207991522205225725492799842956650355099/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (114207991522205225725492799842956650355099/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (91283296356145005974938174951207329859449/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (91283296356145005974938174951207329859449/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2779 BracketBatch0173.bracket2780 (91283296356145005974938174951207329859449/1000000000000000000000000000000000000000) (5971806676905812180777627353512132251199/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2779 BracketBatch0173.bracket2780
  (91283296356145005974938174951207329859449/1000000000000000000000000000000000000000) (5971806676905812180777627353512132251199/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2779
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2780
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (913663932177641805803942398743653202840789/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (913663932177641805803942398743653202840789/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (915331945997974242336414641844072770415557/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (915331945997974242336414641844072770415557/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (914497939087808024070178520293862986628173/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (914497939087808024070178520293862986628173/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2780 BracketBatch0173.bracket2781 (914497939087808024070178520293862986628173/10000000000000000000000000000000000000000) (47796840063401701585048133206041614297/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2780 BracketBatch0173.bracket2781
  (914497939087808024070178520293862986628173/10000000000000000000000000000000000000000) (47796840063401701585048133206041614297/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2780
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2781
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (457665972998987121168207320922036385207777/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (457665972998987121168207320922036385207777/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (229251517448525038710548034782674454479033/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (229251517448525038710548034782674454479033/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (916169007896037198589303390487385294165843/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (916169007896037198589303390487385294165843/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2781 BracketBatch0173.bracket2782 (916169007896037198589303390487385294165843/10000000000000000000000000000000000000000) (2988704276526519457153541679790689889199/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2781 BracketBatch0173.bracket2782
  (916169007896037198589303390487385294165843/10000000000000000000000000000000000000000) (2988704276526519457153541679790689889199/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2781
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2782
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (917006069794100154842192139130697817916129/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (917006069794100154842192139130697817916129/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (918686337198912475205036044913252772550781/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (918686337198912475205036044913252772550781/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (183569240699301263004722818404395059046691/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (183569240699301263004722818404395059046691/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2782 BracketBatch0173.bracket2783 (183569240699301263004722818404395059046691/2000000000000000000000000000000000000000) (5980217330844384579050290855720230671839/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2782 BracketBatch0173.bracket2783
  (183569240699301263004722818404395059046691/2000000000000000000000000000000000000000) (5980217330844384579050290855720230671839/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2782
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2783
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0434.rows BesselBatch0434.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (459343168599456237602518022456626386275389/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (459343168599456237602518022456626386275389/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0435.rows BesselBatch0435.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (460186391046302409366902334992040221995401/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (460186391046302409366902334992040221995401/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0706.rows BesselBatch0706.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (91952955964575864696942035744866660827079/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (91952955964575864696942035744866660827079/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0347.rows ScalarLogs0347.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0173.bracket2783 BracketBatch0174.bracket2784 (91952955964575864696942035744866660827079/1000000000000000000000000000000000000000) (119660627199020519175543640028395582109/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0173.bracket2783 BracketBatch0174.bracket2784
  (91952955964575864696942035744866660827079/1000000000000000000000000000000000000000) (119660627199020519175543640028395582109/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2783
