import BecknerOnofri.EntropyScalarCertificate.Bessel0223
import BecknerOnofri.EntropyScalarCertificate.Bessel0224
import BecknerOnofri.EntropyScalarCertificate.Bessel0225
import BecknerOnofri.EntropyScalarCertificate.Bessel0600
import BecknerOnofri.EntropyScalarCertificate.Bessel0601
import BecknerOnofri.EntropyScalarCertificate.Brackets0089
import BecknerOnofri.EntropyScalarCertificate.Brackets0090
import BecknerOnofri.EntropyScalarCertificate.Logs0179
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1432
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (4243180537454667165583820787786267713039/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4243180537454667165583820787786267713039/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (16981655104403149035484535905165176093327/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16981655104403149035484535905165176093327/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (33954377254221817697819819056310246945483/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33954377254221817697819819056310246945483/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1432 BracketBatch0089.bracket1433 (33954377254221817697819819056310246945483/20000000000000000000000000000000000000000) (640510556829016454971840850585179590877/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1432 BracketBatch0089.bracket1433
  (33954377254221817697819819056310246945483/20000000000000000000000000000000000000000) (640510556829016454971840850585179590877/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1432
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1433
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (4245413776100787258871133976291294023331/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4245413776100787258871133976291294023331/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (16990598774422223245258545904040598117237/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16990598774422223245258545904040598117237/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (33972253878825372280743081809205774210561/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33972253878825372280743081809205774210561/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1433 BracketBatch0089.bracket1434 (33972253878825372280743081809205774210561/20000000000000000000000000000000000000000) (160250691661729181210711453763093845961/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1433 BracketBatch0089.bracket1434
  (33972253878825372280743081809205774210561/20000000000000000000000000000000000000000) (160250691661729181210711453763093845961/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1433
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1434
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (8495299387211111622629272952020299058617/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8495299387211111622629272952020299058617/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (8499776590406939907890011436676056720699/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8499776590406939907890011436676056720699/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (4248768994404512882629821097174088944829/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4248768994404512882629821097174088944829/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1434 BracketBatch0089.bracket1435 (4248768994404512882629821097174088944829/2500000000000000000000000000000000000000) (160373867565861054729612034917747597729/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1434 BracketBatch0089.bracket1435
  (4248768994404512882629821097174088944829/2500000000000000000000000000000000000000) (160373867565861054729612034917747597729/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1434
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1435
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (3399910636162775963156004574670422688279/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3399910636162775963156004574670422688279/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (8504259172284365340799367888531397010157/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8504259172284365340799367888531397010157/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (34008071525382610497378758650414907461709/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34008071525382610497378758650414907461709/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1435 BracketBatch0089.bracket1436 (34008071525382610497378758650414907461709/20000000000000000000000000000000000000000) (5135909347259226264743969878752733197/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1435 BracketBatch0089.bracket1436
  (34008071525382610497378758650414907461709/20000000000000000000000000000000000000000) (5135909347259226264743969878752733197/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1435
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1436
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (17008518344568730681598735777062794020311/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17008518344568730681598735777062794020311/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (17017494286730169056409234618596804741343/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17017494286730169056409234618596804741343/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (17013006315649449869003985197829799380827/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17013006315649449869003985197829799380827/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1436 BracketBatch0089.bracket1437 (17013006315649449869003985197829799380827/10000000000000000000000000000000000000000) (80310295226119534378832639153600706341/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1436 BracketBatch0089.bracket1437
  (17013006315649449869003985197829799380827/10000000000000000000000000000000000000000) (80310295226119534378832639153600706341/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1436
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1437
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (850874714336508452820461730929840237067/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (850874714336508452820461730929840237067/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (17026481028394527850985383216275330205917/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17026481028394527850985383216275330205917/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (34043975315124696907394617834872134947257/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34043975315124696907394617834872134947257/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1437 BracketBatch0089.bracket1438 (34043975315124696907394617834872134947257/20000000000000000000000000000000000000000) (160744137799906560765581764513734590163/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1437 BracketBatch0089.bracket1438
  (34043975315124696907394617834872134947257/20000000000000000000000000000000000000000) (160744137799906560765581764513734590163/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1437
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1438
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (8513240514197263925492691608137665102957/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8513240514197263925492691608137665102957/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (4258869647677809660638109523713142082423/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4258869647677809660638109523713142082423/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (17030979809552883246768910655563949267803/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17030979809552883246768910655563949267803/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1438 BracketBatch0089.bracket1439 (17030979809552883246768910655563949267803/10000000000000000000000000000000000000000) (321735618656149805131131439517074199331/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1438 BracketBatch0089.bracket1439
  (17030979809552883246768910655563949267803/10000000000000000000000000000000000000000) (321735618656149805131131439517074199331/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1438
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1439
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0224.rows BesselBatch0224.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (17035478590711238642552438094852568329689/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17035478590711238642552438094852568329689/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0225.rows BesselBatch0225.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (17044486994882991197828052737048044034627/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17044486994882991197828052737048044034627/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0601.rows BesselBatch0601.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (8519991396398557460095122707975153091079/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8519991396398557460095122707975153091079/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0179.rows ScalarLogs0179.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1439 BracketBatch0090.bracket1440 (8519991396398557460095122707975153091079/5000000000000000000000000000000000000000) (643966420881228863717289781707653942787/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1439 BracketBatch0090.bracket1440
  (8519991396398557460095122707975153091079/5000000000000000000000000000000000000000) (643966420881228863717289781707653942787/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1439
