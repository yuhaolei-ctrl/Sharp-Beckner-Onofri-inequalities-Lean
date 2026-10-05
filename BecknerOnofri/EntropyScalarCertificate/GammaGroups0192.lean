import BecknerOnofri.EntropyScalarCertificate.Bessel0240
import BecknerOnofri.EntropyScalarCertificate.Bessel0241
import BecknerOnofri.EntropyScalarCertificate.Bessel0608
import BecknerOnofri.EntropyScalarCertificate.Bessel0609
import BecknerOnofri.EntropyScalarCertificate.Brackets0096
import BecknerOnofri.EntropyScalarCertificate.Logs0192
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1536
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (17963211556296079543188669945032555152553/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17963211556296079543188669945032555152553/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (1797338142289873305429781916906019922467/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1797338142289873305429781916906019922467/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (35936592979194812597486489114092754377223/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35936592979194812597486489114092754377223/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1536 BracketBatch0096.bracket1537 (35936592979194812597486489114092754377223/20000000000000000000000000000000000000000) (694484380345277708907764587154833420933/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1536 BracketBatch0096.bracket1537
  (35936592979194812597486489114092754377223/20000000000000000000000000000000000000000) (694484380345277708907764587154833420933/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1536
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1537
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (17973381422898733054297819169060199224667/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17973381422898733054297819169060199224667/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (17983564495833450971081124519527592929127/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17983564495833450971081124519527592929127/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (17978472959366092012689471844293896076897/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17978472959366092012689471844293896076897/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1537 BracketBatch0096.bracket1538 (17978472959366092012689471844293896076897/10000000000000000000000000000000000000000) (43439506800710691363419956291231756193/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1537 BracketBatch0096.bracket1538
  (17978472959366092012689471844293896076897/10000000000000000000000000000000000000000) (43439506800710691363419956291231756193/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1537
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1538
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (4495891123958362742770281129881898232281/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4495891123958362742770281129881898232281/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (4498440200616977006274165005132932186367/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4498440200616977006274165005132932186367/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (1124291415571917468630555766876853802331/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1124291415571917468630555766876853802331/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1538 BracketBatch0096.bracket1539 (1124291415571917468630555766876853802331/625000000000000000000000000000000000000) (86947551832277781034056998441771941223/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1538 BracketBatch0096.bracket1539
  (1124291415571917468630555766876853802331/625000000000000000000000000000000000000) (86947551832277781034056998441771941223/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1538
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1539
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (3598752160493581605019332004106345749093/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3598752160493581605019332004106345749093/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (18003970370242221952879833513726851032217/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18003970370242221952879833513726851032217/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (17998865586355064988988246767129289888841/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17998865586355064988988246767129289888841/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1539 BracketBatch0096.bracket1540 (17998865586355064988988246767129289888841/10000000000000000000000000000000000000000) (348064649385613821762134740564199897927/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1539 BracketBatch0096.bracket1540
  (17998865586355064988988246767129289888841/10000000000000000000000000000000000000000) (348064649385613821762134740564199897927/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1539
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1540
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (9001985185121110976439916756863425516107/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9001985185121110976439916756863425516107/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (18014193226669182638644091645671976764301/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18014193226669182638644091645671976764301/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (7203632719382280918304785031879765559303/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7203632719382280918304785031879765559303/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1540 BracketBatch0096.bracket1541 (7203632719382280918304785031879765559303/4000000000000000000000000000000000000000) (696678762037450760556601619250941827061/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1540 BracketBatch0096.bracket1541
  (7203632719382280918304785031879765559303/4000000000000000000000000000000000000000) (696678762037450760556601619250941827061/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1540
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1541
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (9007096613334591319322045822835988382149/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9007096613334591319322045822835988382149/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (4506107349833620526862622192141127439769/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4506107349833620526862622192141127439769/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (18019311313001832373047290207118243261687/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18019311313001832373047290207118243261687/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1541 BracketBatch0096.bracket1542 (18019311313001832373047290207118243261687/10000000000000000000000000000000000000000) (348614402672812777576535160191533370463/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1541 BracketBatch0096.bracket1542
  (18019311313001832373047290207118243261687/10000000000000000000000000000000000000000) (348614402672812777576535160191533370463/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1541
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1542
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0240.rows BesselBatch0240.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (18024429399334482107450488768564509759073/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18024429399334482107450488768564509759073/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (3606935783179389074518094603187536021879/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3606935783179389074518094603187536021879/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (9014777078807856870010240446125547467117/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9014777078807856870010240446125547467117/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1542 BracketBatch0096.bracket1543 (9014777078807856870010240446125547467117/5000000000000000000000000000000000000000) (139555885917231947614929662666066663947/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1542 BracketBatch0096.bracket1543
  (9014777078807856870010240446125547467117/5000000000000000000000000000000000000000) (139555885917231947614929662666066663947/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1542
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1543
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (1127167432243559085786904563496105006837/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1127167432243559085786904563496105006837/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0241.rows BesselBatch0241.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (9022470902044381070473033085632577342521/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9022470902044381070473033085632577342521/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0609.rows BesselBatch0609.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (18039810359992853756768269593601417397217/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18039810359992853756768269593601417397217/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0192.rows ScalarLogs0192.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0096.bracket1543 BracketBatch0096.bracket1544 (18039810359992853756768269593601417397217/10000000000000000000000000000000000000000) (34916531782556904719657222956739844657/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0096.bracket1543 BracketBatch0096.bracket1544
  (18039810359992853756768269593601417397217/10000000000000000000000000000000000000000) (34916531782556904719657222956739844657/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1543
