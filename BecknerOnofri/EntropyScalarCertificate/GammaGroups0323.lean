import BecknerOnofri.EntropyScalarCertificate.Bessel0403
import BecknerOnofri.EntropyScalarCertificate.Bessel0404
import BecknerOnofri.EntropyScalarCertificate.Bessel0405
import BecknerOnofri.EntropyScalarCertificate.Bessel0690
import BecknerOnofri.EntropyScalarCertificate.Bessel0691
import BecknerOnofri.EntropyScalarCertificate.Brackets0161
import BecknerOnofri.EntropyScalarCertificate.Brackets0162
import BecknerOnofri.EntropyScalarCertificate.Logs0323
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2584
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (26651953670421518310970934296746770967681/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26651953670421518310970934296746770967681/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (213941156235579227787319613772925518513539/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (213941156235579227787319613772925518513539/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (427156785598951374275087088146899686254987/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (427156785598951374275087088146899686254987/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2584 BracketBatch0161.bracket2585 (427156785598951374275087088146899686254987/10000000000000000000000000000000000000000) (37585330295860313667701346730780662083/78125000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2584 BracketBatch0161.bracket2585
  (427156785598951374275087088146899686254987/10000000000000000000000000000000000000000) (37585330295860313667701346730780662083/78125000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2584
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2585
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0403.rows BesselBatch0403.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (17115292498846338222985569101834041481083/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17115292498846338222985569101834041481083/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (214671652604250856330669183853159458749827/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (214671652604250856330669183853159458749827/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (857225617679660168235977595252169954526729/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (857225617679660168235977595252169954526729/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2585 BracketBatch0161.bracket2586 (857225617679660168235977595252169954526729/20000000000000000000000000000000000000000) (4815914214164778650264040931346255912621/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2585 BracketBatch0161.bracket2586
  (857225617679660168235977595252169954526729/20000000000000000000000000000000000000000) (4815914214164778650264040931346255912621/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2585
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2586
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (429343305208501712661338367706318917499651/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (429343305208501712661338367706318917499651/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (430814339402576427053597425063027747582587/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (430814339402576427053597425063027747582587/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0690.rows BesselBatch0690.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (430078822305539069857467896384673332541119/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (430078822305539069857467896384673332541119/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2586 BracketBatch0161.bracket2587 (430078822305539069857467896384673332541119/10000000000000000000000000000000000000000) (482092371688282130753490701028439596271/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2586 BracketBatch0161.bracket2587
  (430078822305539069857467896384673332541119/10000000000000000000000000000000000000000) (482092371688282130753490701028439596271/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2586
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2587
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (53851792425322053381699678132878468447823/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (53851792425322053381699678132878468447823/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (27018469933154925037246017256471275002287/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (27018469933154925037246017256471275002287/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (107888732291631903456191712645821018452397/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (107888732291631903456191712645821018452397/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2587 BracketBatch0161.bracket2588 (107888732291631903456191712645821018452397/2500000000000000000000000000000000000000) (603243862426100293764120837034626008869/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2587 BracketBatch0161.bracket2588
  (107888732291631903456191712645821018452397/2500000000000000000000000000000000000000) (603243862426100293764120837034626008869/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2587
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2588
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (432295518930478800595936276103540400036589/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (432295518930478800595936276103540400036589/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (8675738982141006493090380617062916783981/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8675738982141006493090380617062916783981/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (866082468037529125250455306956686239235639/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (866082468037529125250455306956686239235639/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2588 BracketBatch0161.bracket2589 (866082468037529125250455306956686239235639/20000000000000000000000000000000000000000) (966199175233346977934002099391217928013/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2588 BracketBatch0161.bracket2589
  (866082468037529125250455306956686239235639/20000000000000000000000000000000000000000) (966199175233346977934002099391217928013/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2588
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2589
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (433786949107050324654519030853145839199047/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (433786949107050324654519030853145839199047/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (108822184177459658957724204911899631357747/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (108822184177459658957724204911899631357747/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (173815137163377792097083170100148872926007/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (173815137163377792097083170100148872926007/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2589 BracketBatch0161.bracket2590 (173815137163377792097083170100148872926007/4000000000000000000000000000000000000000) (2418029381315878972235862130629027715519/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2589 BracketBatch0161.bracket2590
  (173815137163377792097083170100148872926007/4000000000000000000000000000000000000000) (2418029381315878972235862130629027715519/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2589
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2590
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (87057747341967727166179363929519705086197/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (87057747341967727166179363929519705086197/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (218400495002290100705966039271724212138531/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (218400495002290100705966039271724212138531/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (872089726714418837242828898191046949708047/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (872089726714418837242828898191046949708047/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2590 BracketBatch0161.bracket2591 (872089726714418837242828898191046949708047/20000000000000000000000000000000000000000) (121028491883548532661386697501540535671/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2590 BracketBatch0161.bracket2591
  (872089726714418837242828898191046949708047/20000000000000000000000000000000000000000) (121028491883548532661386697501540535671/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2590
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2591
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0404.rows BesselBatch0404.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (436800990004580201411932078543448424277059/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (436800990004580201411932078543448424277059/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0405.rows BesselBatch0405.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (8766476375424352132247685875625605501017/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8766476375424352132247685875625605501017/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0691.rows BesselBatch0691.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (875124808775797808024316372324728699327909/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (875124808775797808024316372324728699327909/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0323.rows ScalarLogs0323.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0161.bracket2591 BracketBatch0162.bracket2592 (875124808775797808024316372324728699327909/20000000000000000000000000000000000000000) (1211559682977557340874527503292957118907/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0161.bracket2591 BracketBatch0162.bracket2592
  (875124808775797808024316372324728699327909/20000000000000000000000000000000000000000) (1211559682977557340874527503292957118907/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2591
