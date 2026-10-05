import BecknerOnofri.EntropyScalarCertificate.Bessel0228
import BecknerOnofri.EntropyScalarCertificate.Bessel0229
import BecknerOnofri.EntropyScalarCertificate.Bessel0230
import BecknerOnofri.EntropyScalarCertificate.Bessel0603
import BecknerOnofri.EntropyScalarCertificate.Brackets0091
import BecknerOnofri.EntropyScalarCertificate.Brackets0092
import BecknerOnofri.EntropyScalarCertificate.Logs0183
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1464
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (43159993322844393312712255138360466093/25000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (43159993322844393312712255138360466093/25000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1727328382967327121922899895326619075231/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1727328382967327121922899895326619075231/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (3453728115881102854431390100861037718951/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3453728115881102854431390100861037718951/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1464 BracketBatch0091.bracket1465 (3453728115881102854431390100861037718951/2000000000000000000000000000000000000000) (32825492968439513618379577348800953759/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1464 BracketBatch0091.bracket1465
  (3453728115881102854431390100861037718951/2000000000000000000000000000000000000000) (32825492968439513618379577348800953759/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1464
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1465
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0228.rows BesselBatch0228.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (17273283829673271219228998953266190752307/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17273283829673271219228998953266190752307/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (17282581742563459028197693910465006364509/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17282581742563459028197693910465006364509/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (2159741598264795640464168303983199819801/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2159741598264795640464168303983199819801/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1465 BracketBatch0091.bracket1466 (2159741598264795640464168303983199819801/1250000000000000000000000000000000000000) (131403647812568736153616063307716985537/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1465 BracketBatch0091.bracket1466
  (2159741598264795640464168303983199819801/1250000000000000000000000000000000000000) (131403647812568736153616063307716985537/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1465
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1466
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (8641290871281729514098846955232503182253/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8641290871281729514098846955232503182253/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (17291891090511367466929632977844135025371/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17291891090511367466929632977844135025371/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (34574472833074826495127326888309141389877/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34574472833074826495127326888309141389877/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1466 BracketBatch0091.bracket1467 (34574472833074826495127326888309141389877/20000000000000000000000000000000000000000) (328763568282156725362032110530631862869/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1466 BracketBatch0091.bracket1467
  (34574472833074826495127326888309141389877/20000000000000000000000000000000000000000) (328763568282156725362032110530631862869/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1466
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1467
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (2161486386313920933366204122230516878171/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2161486386313920933366204122230516878171/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1081325743517375142597872423378868539939/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1081325743517375142597872423378868539939/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (4324137873348671218561948968988253958049/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4324137873348671218561948968988253958049/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1467 BracketBatch0091.bracket1468 (4324137873348671218561948968988253958049/2500000000000000000000000000000000000000) (329018276323407601892714401881245324553/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1467 BracketBatch0091.bracket1468
  (4324137873348671218561948968988253958049/2500000000000000000000000000000000000000) (329018276323407601892714401881245324553/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1467
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1468
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (17301211896278002281565958774061896639021/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17301211896278002281565958774061896639021/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1081909011417656553103963204067950175071/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1081909011417656553103963204067950175071/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (34611756078960507131229370039149099440157/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34611756078960507131229370039149099440157/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1468 BracketBatch0091.bracket1469 (34611756078960507131229370039149099440157/20000000000000000000000000000000000000000) (26341859523416437332723843565896052509/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1468 BracketBatch0091.bracket1469
  (34611756078960507131229370039149099440157/20000000000000000000000000000000000000000) (26341859523416437332723843565896052509/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1468
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1469
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (17310544182682504849663411265087202801133/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17310544182682504849663411265087202801133/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (8659943986301164703142506230297052966033/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8659943986301164703142506230297052966033/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (34630432155284834255948423725681308733199/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34630432155284834255948423725681308733199/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1469 BracketBatch0091.bracket1470 (34630432155284834255948423725681308733199/20000000000000000000000000000000000000000) (659056943656611855896308329162440313057/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1469 BracketBatch0091.bracket1470
  (34630432155284834255948423725681308733199/20000000000000000000000000000000000000000) (659056943656611855896308329162440313057/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1469
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1470
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (17319887972602329406285012460594105932063/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17319887972602329406285012460594105932063/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (17329243288973420898562062157789110849333/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17329243288973420898562062157789110849333/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (8662282815393937576211768654595804195349/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8662282815393937576211768654595804195349/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1470 BracketBatch0091.bracket1471 (8662282815393937576211768654595804195349/5000000000000000000000000000000000000000) (13191358402767625366527316861635727943/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1470 BracketBatch0091.bracket1471
  (8662282815393937576211768654595804195349/5000000000000000000000000000000000000000) (13191358402767625366527316861635727943/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1470
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1471
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0229.rows BesselBatch0229.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (1732924328897342089856206215778911084933/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1732924328897342089856206215778911084933/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0230.rows BesselBatch0230.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (17338610154790393471333984875837301070097/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17338610154790393471333984875837301070097/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0603.rows BesselBatch0603.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (34667853443763814369896047033626411919427/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34667853443763814369896047033626411919427/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0183.rows ScalarLogs0183.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0091.bracket1471 BracketBatch0092.bracket1472 (34667853443763814369896047033626411919427/20000000000000000000000000000000000000000) (330039709155068705158793410570674526443/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0091.bracket1471 BracketBatch0092.bracket1472
  (34667853443763814369896047033626411919427/20000000000000000000000000000000000000000) (330039709155068705158793410570674526443/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1471
