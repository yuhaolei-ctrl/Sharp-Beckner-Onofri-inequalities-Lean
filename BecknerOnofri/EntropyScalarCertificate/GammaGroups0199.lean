import BecknerOnofri.EntropyScalarCertificate.Bessel0248
import BecknerOnofri.EntropyScalarCertificate.Bessel0249
import BecknerOnofri.EntropyScalarCertificate.Bessel0250
import BecknerOnofri.EntropyScalarCertificate.Bessel0613
import BecknerOnofri.EntropyScalarCertificate.Brackets0099
import BecknerOnofri.EntropyScalarCertificate.Brackets0100
import BecknerOnofri.EntropyScalarCertificate.Logs0199
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1592
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (4638461995188144486534763640258705882409/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4638461995188144486534763640258705882409/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (9282400821913416828865372257312519914469/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9282400821913416828865372257312519914469/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (18559324812289705801934899537829931679287/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18559324812289705801934899537829931679287/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1592 BracketBatch0099.bracket1593 (18559324812289705801934899537829931679287/10000000000000000000000000000000000000000) (4537946932417529397278046809038062697/62500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1592 BracketBatch0099.bracket1593
  (18559324812289705801934899537829931679287/10000000000000000000000000000000000000000) (4537946932417529397278046809038062697/62500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1592
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1593
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0248.rows BesselBatch0248.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (3712960328765366731546148902925007965787/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3712960328765366731546148902925007965787/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (4643942541016086805763602769642275220513/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4643942541016086805763602769642275220513/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (37140571807891180880785155593194140710987/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37140571807891180880785155593194140710987/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1593 BracketBatch0099.bracket1594 (37140571807891180880785155593194140710987/20000000000000000000000000000000000000000) (181663245485220308894814185614686293237/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1593 BracketBatch0099.bracket1594
  (37140571807891180880785155593194140710987/20000000000000000000000000000000000000000) (181663245485220308894814185614686293237/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1593
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1594
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (18575770164064347223054411078569100882049/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18575770164064347223054411078569100882049/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (18586753573267511634451643037697444737603/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18586753573267511634451643037697444737603/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (9290630934332964714376513529066636404913/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9290630934332964714376513529066636404913/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1594 BracketBatch0099.bracket1595 (9290630934332964714376513529066636404913/5000000000000000000000000000000000000000) (363617542159824696613217449373366425421/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1594 BracketBatch0099.bracket1595
  (9290630934332964714376513529066636404913/5000000000000000000000000000000000000000) (363617542159824696613217449373366425421/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1594
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1595
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (11616720983292194771532276898560902961/6250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11616720983292194771532276898560902961/6250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (9298875951662708090414815618220135353259/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9298875951662708090414815618220135353259/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (18592252738296463907640637137068857722059/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18592252738296463907640637137068857722059/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1595 BracketBatch0099.bracket1596 (18592252738296463907640637137068857722059/10000000000000000000000000000000000000000) (727817817307163448475821546793104231779/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1595 BracketBatch0099.bracket1596
  (18592252738296463907640637137068857722059/10000000000000000000000000000000000000000) (727817817307163448475821546793104231779/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1595
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1596
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (3719550380665083236165926247288054141303/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3719550380665083236165926247288054141303/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (2326095648276766197694678531292875279937/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2326095648276766197694678531292875279937/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (37206517089539545762387059486783272946011/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37206517089539545762387059486783272946011/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1596 BracketBatch0099.bracket1597 (37206517089539545762387059486783272946011/20000000000000000000000000000000000000000) (728401181889341708070642819482558344221/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1596 BracketBatch0099.bracket1597
  (37206517089539545762387059486783272946011/20000000000000000000000000000000000000000) (728401181889341708070642819482558344221/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1596
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1597
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (18608765186214129581557428250343002239493/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18608765186214129581557428250343002239493/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (116373709087481151342683825680782689691/62500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (116373709087481151342683825680782689691/62500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (37228558640211113796386840359268232590053/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37228558640211113796386840359268232590053/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1597 BracketBatch0099.bracket1598 (37228558640211113796386840359268232590053/20000000000000000000000000000000000000000) (364492589526985133100987801288082422731/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1597 BracketBatch0099.bracket1598
  (37228558640211113796386840359268232590053/20000000000000000000000000000000000000000) (364492589526985133100987801288082422731/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1597
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1598
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (18619793453996984214829412108925230350557/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18619793453996984214829412108925230350557/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (9315418369412430722784135167145681052467/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9315418369412430722784135167145681052467/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (37250630192821845660397682443216592455491/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37250630192821845660397682443216592455491/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1598 BracketBatch0099.bracket1599 (37250630192821845660397682443216592455491/20000000000000000000000000000000000000000) (182392452447676691555143862595711542343/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1598 BracketBatch0099.bracket1599
  (37250630192821845660397682443216592455491/20000000000000000000000000000000000000000) (182392452447676691555143862595711542343/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1598
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1599
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0249.rows BesselBatch0249.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (18630836738824861445568270334291362104931/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18630836738824861445568270334291362104931/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0250.rows BesselBatch0250.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (18641895072936478057968135050916641189219/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18641895072936478057968135050916641189219/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0613.rows BesselBatch0613.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (745454636235226790070728107704160065883/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (745454636235226790070728107704160065883/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0199.rows ScalarLogs0199.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0099.bracket1599 BracketBatch0100.bracket1600 (745454636235226790070728107704160065883/400000000000000000000000000000000000000) (365077537545542085714348692676489916237/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0099.bracket1599 BracketBatch0100.bracket1600
  (745454636235226790070728107704160065883/400000000000000000000000000000000000000) (365077537545542085714348692676489916237/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1599
