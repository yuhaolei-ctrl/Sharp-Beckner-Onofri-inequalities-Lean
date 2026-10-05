import BecknerOnofri.EntropyScalarCertificate.Bessel0161
import BecknerOnofri.EntropyScalarCertificate.Bessel0162
import BecknerOnofri.EntropyScalarCertificate.Bessel0569
import BecknerOnofri.EntropyScalarCertificate.Bessel0570
import BecknerOnofri.EntropyScalarCertificate.Brackets0064
import BecknerOnofri.EntropyScalarCertificate.Brackets0065
import BecknerOnofri.EntropyScalarCertificate.Logs0129
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1032
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (37623019012171279482126967559356300423/62500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (37623019012171279482126967559356300423/62500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (150897241877395691049381436580268706169/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (150897241877395691049381436580268706169/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (301389317926080808977889306817693907861/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (301389317926080808977889306817693907861/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1032 BracketBatch0064.bracket1033 (301389317926080808977889306817693907861/500000000000000000000000000000000000000) (12272880359237374097488104944001986073/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1032 BracketBatch0064.bracket1033
  (301389317926080808977889306817693907861/500000000000000000000000000000000000000) (12272880359237374097488104944001986073/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1032
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1033
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (6035889675095827641975257463210748246757/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6035889675095827641975257463210748246757/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (6052133774535716705407814336359650441607/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6052133774535716705407814336359650441607/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (3022005862407886086845767949892599672091/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3022005862407886086845767949892599672091/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1033 BracketBatch0064.bracket1034 (3022005862407886086845767949892599672091/5000000000000000000000000000000000000000) (3867374268556772776035795562493194547/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1033 BracketBatch0064.bracket1034
  (3022005862407886086845767949892599672091/5000000000000000000000000000000000000000) (3867374268556772776035795562493194547/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1033
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1034
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (1513033443633929176351953584089912610401/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1513033443633929176351953584089912610401/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (379275973139285302156924584070803604329/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (379275973139285302156924584070803604329/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (3030137336191070384979651920373127027717/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3030137336191070384979651920373127027717/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1034 BracketBatch0064.bracket1035 (3030137336191070384979651920373127027717/5000000000000000000000000000000000000000) (62395052488910514979430116226618054019/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1034 BracketBatch0064.bracket1035
  (3030137336191070384979651920373127027717/5000000000000000000000000000000000000000) (62395052488910514979430116226618054019/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1034
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1035
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (6068415570228564834510793345132857669261/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6068415570228564834510793345132857669261/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (6084735293987492060174457745016198059077/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6084735293987492060174457745016198059077/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (6076575432108028447342625545074527864169/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6076575432108028447342625545074527864169/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1035 BracketBatch0064.bracket1036 (6076575432108028447342625545074527864169/10000000000000000000000000000000000000000) (12583122794962393653244696862855620021/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1035 BracketBatch0064.bracket1036
  (6076575432108028447342625545074527864169/10000000000000000000000000000000000000000) (12583122794962393653244696862855620021/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1035
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1036
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (3042367646993746030087228872508099029537/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3042367646993746030087228872508099029537/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (762636647437133771261721964793978553841/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (762636647437133771261721964793978553841/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (6092914236742281115134116731684013244901/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6092914236742281115134116731684013244901/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1036 BracketBatch0064.bracket1037 (6092914236742281115134116731684013244901/10000000000000000000000000000000000000000) (3171984623503782831093718840454036541/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1036 BracketBatch0064.bracket1037
  (6092914236742281115134116731684013244901/10000000000000000000000000000000000000000) (3171984623503782831093718840454036541/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1036
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1037
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (244043727179882806803751028734073137229/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (244043727179882806803751028734073137229/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (6117489462333405038550424311915316255133/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6117489462333405038550424311915316255133/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (6109291320915237604322100015133572342929/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6109291320915237604322100015133572342929/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1037 BracketBatch0064.bracket1038 (6109291320915237604322100015133572342929/10000000000000000000000000000000000000000) (31983653901981943926458751288384643773/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1037 BracketBatch0064.bracket1038
  (6109291320915237604322100015133572342929/10000000000000000000000000000000000000000) (31983653901981943926458751288384643773/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1037
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1038
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (611748946233340503855042431191531625513/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (611748946233340503855042431191531625513/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (6133924379984480584977763818564183600669/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6133924379984480584977763818564183600669/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (12251413842317885623528188130479499855799/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12251413842317885623528188130479499855799/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1038 BracketBatch0064.bracket1039 (12251413842317885623528188130479499855799/20000000000000000000000000000000000000000) (64498479920505218805160708083041285111/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1038 BracketBatch0064.bracket1039
  (12251413842317885623528188130479499855799/20000000000000000000000000000000000000000) (64498479920505218805160708083041285111/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1038
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1039
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (3066962189992240292488881909282091800333/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3066962189992240292488881909282091800333/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (6150398171870768382812219034280783096691/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6150398171870768382812219034280783096691/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (12284322551855248967789982852844966697357/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12284322551855248967789982852844966697357/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0129.rows ScalarLogs0129.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1039 BracketBatch0065.bracket1040 (12284322551855248967789982852844966697357/20000000000000000000000000000000000000000) (32516614439736645491881167096692283211/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1039 BracketBatch0065.bracket1040
  (12284322551855248967789982852844966697357/20000000000000000000000000000000000000000) (32516614439736645491881167096692283211/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1039
