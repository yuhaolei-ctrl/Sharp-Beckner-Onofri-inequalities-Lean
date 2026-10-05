import BecknerOnofri.EntropyScalarCertificate.Bessel0175
import BecknerOnofri.EntropyScalarCertificate.Bessel0176
import BecknerOnofri.EntropyScalarCertificate.Bessel0576
import BecknerOnofri.EntropyScalarCertificate.Bessel0577
import BecknerOnofri.EntropyScalarCertificate.Brackets0070
import BecknerOnofri.EntropyScalarCertificate.Logs0140
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1120
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (7619787364572175825375431039736725940963/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7619787364572175825375431039736725940963/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (7640433530528790179314833777077519767323/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7640433530528790179314833777077519767323/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (7630110447550483002345132408407122854143/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7630110447550483002345132408407122854143/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1120 BracketBatch0070.bracket1121 (7630110447550483002345132408407122854143/10000000000000000000000000000000000000000) (61153522117345836984061847978186213517/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1120 BracketBatch0070.bracket1121
  (7630110447550483002345132408407122854143/10000000000000000000000000000000000000000) (61153522117345836984061847978186213517/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1120
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1121
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (191010838263219754482870844426937994183/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (191010838263219754482870844426937994183/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (7661147467471320340571140004062682237143/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7661147467471320340571140004062682237143/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (15301580998000110519885973781140202004463/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15301580998000110519885973781140202004463/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1121 BracketBatch0070.bracket1122 (15301580998000110519885973781140202004463/20000000000000000000000000000000000000000) (123215814780583743413403987014149075331/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1121 BracketBatch0070.bracket1122
  (15301580998000110519885973781140202004463/20000000000000000000000000000000000000000) (123215814780583743413403987014149075331/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1121
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1122
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (383057373373566017028557000203134111857/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (383057373373566017028557000203134111857/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (7681929685407463309707908132632664101151/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7681929685407463309707908132632664101151/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (15343077152878783650279048136695346338291/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15343077152878783650279048136695346338291/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1122 BracketBatch0070.bracket1123 (15343077152878783650279048136695346338291/20000000000000000000000000000000000000000) (124130336813507637897809075509428160631/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1122 BracketBatch0070.bracket1123
  (15343077152878783650279048136695346338291/20000000000000000000000000000000000000000) (124130336813507637897809075509428160631/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1122
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1123
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (1920482421351865827426977033158166025287/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1920482421351865827426977033158166025287/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (7702780699599853895658887978784127975453/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7702780699599853895658887978784127975453/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (15384710385007317205366796111416792076601/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15384710385007317205366796111416792076601/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1123 BracketBatch0070.bracket1124 (15384710385007317205366796111416792076601/20000000000000000000000000000000000000000) (62525322455216155471867280454700101509/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1123 BracketBatch0070.bracket1124
  (15384710385007317205366796111416792076601/20000000000000000000000000000000000000000) (62525322455216155471867280454700101509/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1123
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1124
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (154055613991997077913177759575682559509/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (154055613991997077913177759575682559509/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (308948041225451173386076965106242433519/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (308948041225451173386076965106242433519/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (617059269209445329212432484257607552537/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (617059269209445329212432484257607552537/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1124 BracketBatch0070.bracket1125 (617059269209445329212432484257607552537/800000000000000000000000000000000000000) (31494193477731449367928787613017616399/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1124 BracketBatch0070.bracket1125
  (617059269209445329212432484257607552537/800000000000000000000000000000000000000) (31494193477731449367928787613017616399/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1124
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1125
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1930925257659069833662981031914015209493/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1930925257659069833662981031914015209493/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (3872345602250515390450609030030683425417/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3872345602250515390450609030030683425417/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (7734196117568655057776571093858713844403/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7734196117568655057776571093858713844403/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1125 BracketBatch0070.bracket1126 (7734196117568655057776571093858713844403/10000000000000000000000000000000000000000) (31727189730046565947781852364072762293/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1125 BracketBatch0070.bracket1126
  (7734196117568655057776571093858713844403/10000000000000000000000000000000000000000) (31727189730046565947781852364072762293/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1125
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1126
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0175.rows BesselBatch0175.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (7744691204501030780901218060061366850831/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7744691204501030780901218060061366850831/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (7765751752647413212708264580492951897629/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7765751752647413212708264580492951897629/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (775522147857422199680474132027715937423/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (775522147857422199680474132027715937423/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1126 BracketBatch0070.bracket1127 (775522147857422199680474132027715937423/1000000000000000000000000000000000000000) (63923317656059642516787835183819237961/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1126 BracketBatch0070.bracket1127
  (775522147857422199680474132027715937423/1000000000000000000000000000000000000000) (63923317656059642516787835183819237961/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1126
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1127
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (3882875876323706606354132290246475948813/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3882875876323706606354132290246475948813/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0176.rows BesselBatch0176.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (3893441606035717881535381013003965277549/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3893441606035717881535381013003965277549/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0576.rows BesselBatch0576.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (3888158741179712243944756651625220613181/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3888158741179712243944756651625220613181/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0140.rows ScalarLogs0140.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0070.bracket1127 BracketBatch0070.bracket1128 (3888158741179712243944756651625220613181/5000000000000000000000000000000000000000) (64395219366231087665859638733531800811/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0070.bracket1127 BracketBatch0070.bracket1128
  (3888158741179712243944756651625220613181/5000000000000000000000000000000000000000) (64395219366231087665859638733531800811/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1127
