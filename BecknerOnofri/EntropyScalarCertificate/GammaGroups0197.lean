module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0246
public import BecknerOnofri.EntropyScalarCertificate.Bessel0247
public import BecknerOnofri.EntropyScalarCertificate.Bessel0612
public import BecknerOnofri.EntropyScalarCertificate.Brackets0098
public import BecknerOnofri.EntropyScalarCertificate.Brackets0099
public import BecknerOnofri.EntropyScalarCertificate.Logs0197
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1576
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (9190292163359274619766258609023525029541/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9190292163359274619766258609023525029541/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (4597826132660669279682624339030354124353/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4597826132660669279682624339030354124353/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (18385944428680613179131507287084233278247/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18385944428680613179131507287084233278247/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1576 BracketBatch0098.bracket1577 (18385944428680613179131507287084233278247/10000000000000000000000000000000000000000) (716852778258655975935974666858082280039/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1576 BracketBatch0098.bracket1577
  (18385944428680613179131507287084233278247/10000000000000000000000000000000000000000) (716852778258655975935974666858082280039/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1576
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1577
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (18391304530642677118730497356121416497409/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18391304530642677118730497356121416497409/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (18402039094455599067104616850803001672919/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18402039094455599067104616850803001672919/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (4599167953137284523229389275865552271291/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4599167953137284523229389275865552271291/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1577 BracketBatch0098.bracket1578 (4599167953137284523229389275865552271291/2500000000000000000000000000000000000000) (717424309342402614158071840176098444367/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1577 BracketBatch0098.bracket1578
  (4599167953137284523229389275865552271291/2500000000000000000000000000000000000000) (717424309342402614158071840176098444367/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1577
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1578
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (4600509773613899766776154212700750418229/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4600509773613899766776154212700750418229/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (1150799253038137480480963187856823039921/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1150799253038137480480963187856823039921/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (9203706785766449688700006964128042577913/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9203706785766449688700006964128042577913/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1578 BracketBatch0098.bracket1579 (9203706785766449688700006964128042577913/5000000000000000000000000000000000000000) (89749556819556682542030954274548780831/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1578 BracketBatch0098.bracket1579
  (9203706785766449688700006964128042577913/5000000000000000000000000000000000000000) (89749556819556682542030954274548780831/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1578
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1579
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (18412788048610199687695411005709168638733/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18412788048610199687695411005709168638733/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (9211775711820837276628295626550981026353/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9211775711820837276628295626550981026353/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (36836339472251874240952002258811130691439/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36836339472251874240952002258811130691439/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1579 BracketBatch0098.bracket1580 (36836339472251874240952002258811130691439/20000000000000000000000000000000000000000) (718569214855541379124829392248533789799/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1579 BracketBatch0098.bracket1580
  (36836339472251874240952002258811130691439/20000000000000000000000000000000000000000) (718569214855541379124829392248533789799/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1579
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1580
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0246.rows BesselBatch0246.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (18423551423641674553256591253101962052703/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18423551423641674553256591253101962052703/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (4608582312541949124025301778657901900643/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4608582312541949124025301778657901900643/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (1474315226952378841974311934709342786211/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1474315226952378841974311934709342786211/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1580 BracketBatch0098.bracket1581 (1474315226952378841974311934709342786211/800000000000000000000000000000000000000) (143828518239240884558766378280460704093/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1580 BracketBatch0098.bracket1581
  (1474315226952378841974311934709342786211/800000000000000000000000000000000000000) (143828518239240884558766378280460704093/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1580
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1581
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (18434329250167796496101207114631607602569/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18434329250167796496101207114631607602569/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (9222560779444591457481611539000740816563/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9222560779444591457481611539000740816563/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (7375890161811395882212886038526617847139/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7375890161811395882212886038526617847139/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1581 BracketBatch0098.bracket1582 (7375890161811395882212886038526617847139/4000000000000000000000000000000000000000) (719716584536789444825238920796323426803/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1581 BracketBatch0098.bracket1582
  (7375890161811395882212886038526617847139/4000000000000000000000000000000000000000) (719716584536789444825238920796323426803/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1581
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1582
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (18445121558889182914963223078001481633123/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18445121558889182914963223078001481633123/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (9227964190294782051758916196972182638171/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9227964190294782051758916196972182638171/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (7380209987895749403696211094389169381893/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7380209987895749403696211094389169381893/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1582 BracketBatch0098.bracket1583 (7380209987895749403696211094389169381893/4000000000000000000000000000000000000000) (720291195837455721910109836667645096583/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1582 BracketBatch0098.bracket1583
  (7380209987895749403696211094389169381893/4000000000000000000000000000000000000000) (720291195837455721910109836667645096583/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1582
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1583
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (18455928380589564103517832393944365276339/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18455928380589564103517832393944365276339/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0247.rows BesselBatch0247.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (2308343718267006575653670723298020510223/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2308343718267006575653670723298020510223/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0612.rows BesselBatch0612.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (36922678126725616708747198180328529358123/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36922678126725616708747198180328529358123/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0197.rows ScalarLogs0197.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0098.bracket1583 BracketBatch0099.bracket1584 (36922678126725616708747198180328529358123/20000000000000000000000000000000000000000) (18021660651504464609598245079312582491/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0098.bracket1583 BracketBatch0099.bracket1584
  (36922678126725616708747198180328529358123/20000000000000000000000000000000000000000) (18021660651504464609598245079312582491/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1583
