module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0287
public import BecknerOnofri.EntropyScalarCertificate.Bessel0288
public import BecknerOnofri.EntropyScalarCertificate.Bessel0632
public import BecknerOnofri.EntropyScalarCertificate.Bessel0633
public import BecknerOnofri.EntropyScalarCertificate.Brackets0115
public import BecknerOnofri.EntropyScalarCertificate.Logs0230
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1840
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (4522885579014467348853095510547485100987/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4522885579014467348853095510547485100987/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (22700853298869774739387246392756797973127/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22700853298869774739387246392756797973127/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (22657640596971055741826361972747111739031/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (22657640596971055741826361972747111739031/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1840 BracketBatch0115.bracket1841 (22657640596971055741826361972747111739031/10000000000000000000000000000000000000000) (927580344853809742786655024851405558583/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1840 BracketBatch0115.bracket1841
  (22657640596971055741826361972747111739031/10000000000000000000000000000000000000000) (927580344853809742786655024851405558583/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1840
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1841
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (5675213324717443684846811598189199493281/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5675213324717443684846811598189199493281/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (5697007467962548419032251713336485985973/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5697007467962548419032251713336485985973/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (5686110396339996051939531655762842739627/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5686110396339996051939531655762842739627/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1841 BracketBatch0115.bracket1842 (5686110396339996051939531655762842739627/2500000000000000000000000000000000000000) (465835066133868610879122105211379796671/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1841 BracketBatch0115.bracket1842
  (5686110396339996051939531655762842739627/2500000000000000000000000000000000000000) (465835066133868610879122105211379796671/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1841
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1842
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (22788029871850193676129006853345943943889/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (22788029871850193676129006853345943943889/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (4575193482526655462878249772211249187823/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4575193482526655462878249772211249187823/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (11415999321120867747630063928600547470751/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11415999321120867747630063928600547470751/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1842 BracketBatch0115.bracket1843 (11415999321120867747630063928600547470751/5000000000000000000000000000000000000000) (935785486313100683844277429062227237527/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1842 BracketBatch0115.bracket1843
  (11415999321120867747630063928600547470751/5000000000000000000000000000000000000000) (935785486313100683844277429062227237527/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1842
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1843
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0287.rows BesselBatch0287.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (2859495926579159664298906107632030742389/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2859495926579159664298906107632030742389/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (22964675883861904417416046665470940664779/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22964675883861904417416046665470940664779/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (45840643296495181731807295526527186603891/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (45840643296495181731807295526527186603891/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1843 BracketBatch0115.bracket1844 (45840643296495181731807295526527186603891/20000000000000000000000000000000000000000) (939926627496692112403810566776124585497/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1843 BracketBatch0115.bracket1844
  (45840643296495181731807295526527186603891/20000000000000000000000000000000000000000) (939926627496692112403810566776124585497/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1843
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1844
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (2870584485482738052177005833183867583097/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2870584485482738052177005833183867583097/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (720442669238651380231752070605641444371/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (720442669238651380231752070605641444371/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0632.rows BesselBatch0632.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (5752355162437343573104014115606433360581/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5752355162437343573104014115606433360581/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1844 BracketBatch0115.bracket1845 (5752355162437343573104014115606433360581/2500000000000000000000000000000000000000) (236023444658376233603154768588139513861/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1844 BracketBatch0115.bracket1845
  (5752355162437343573104014115606433360581/2500000000000000000000000000000000000000) (236023444658376233603154768588139513861/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1844
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1845
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (23054165415636844167416066259380526219869/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (23054165415636844167416066259380526219869/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (23144446309040834066300485287876771494081/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (23144446309040834066300485287876771494081/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (923972234493553564674331030945145954279/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (923972234493553564674331030945145954279/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1845 BracketBatch0115.bracket1846 (923972234493553564674331030945145954279/400000000000000000000000000000000000000) (37931486595203133955408919338891506839/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1845 BracketBatch0115.bracket1846
  (923972234493553564674331030945145954279/400000000000000000000000000000000000000) (37931486595203133955408919338891506839/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1845
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1846
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (11572223154520417033150242643938385747039/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11572223154520417033150242643938385747039/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (23235529039754835115323718055671579119463/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (23235529039754835115323718055671579119463/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (46379975348795669181624203343548350613541/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (46379975348795669181624203343548350613541/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1846 BracketBatch0115.bracket1847 (46379975348795669181624203343548350613541/20000000000000000000000000000000000000000) (238126753442171316146523825555648672233/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1846 BracketBatch0115.bracket1847
  (46379975348795669181624203343548350613541/20000000000000000000000000000000000000000) (238126753442171316146523825555648672233/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1846
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1847
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1161776451987741755766185902783578955973/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1161776451987741755766185902783578955973/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0288.rows BesselBatch0288.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (11663712130884679156238979940506592874967/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11663712130884679156238979940506592874967/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0633.rows BesselBatch0633.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (23281476650762096713900838968342382434697/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (23281476650762096713900838968342382434697/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0230.rows ScalarLogs0230.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0115.bracket1847 BracketBatch0115.bracket1848 (23281476650762096713900838968342382434697/10000000000000000000000000000000000000000) (478376777621196108083789410286930090551/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0115.bracket1847 BracketBatch0115.bracket1848
  (23281476650762096713900838968342382434697/10000000000000000000000000000000000000000) (478376777621196108083789410286930090551/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1847
