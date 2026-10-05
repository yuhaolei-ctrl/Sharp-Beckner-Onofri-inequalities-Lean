module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0413
public import BecknerOnofri.EntropyScalarCertificate.Bessel0414
public import BecknerOnofri.EntropyScalarCertificate.Bessel0415
public import BecknerOnofri.EntropyScalarCertificate.Bessel0695
public import BecknerOnofri.EntropyScalarCertificate.Bessel0696
public import BecknerOnofri.EntropyScalarCertificate.Brackets0165
public import BecknerOnofri.EntropyScalarCertificate.Brackets0166
public import BecknerOnofri.EntropyScalarCertificate.Logs0331
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2648
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (272368493392325738774256587778743102605323/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (272368493392325738774256587778743102605323/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (547110215916130775172581557793201407773683/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (547110215916130775172581557793201407773683/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (1091847202700782252721094733350687612984329/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1091847202700782252721094733350687612984329/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2648 BracketBatch0165.bracket2649 (1091847202700782252721094733350687612984329/20000000000000000000000000000000000000000) (2585650996958952495013392980547749286127/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2648 BracketBatch0165.bracket2649
  (1091847202700782252721094733350687612984329/20000000000000000000000000000000000000000) (2585650996958952495013392980547749286127/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2648
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2649
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (6838877698951634689657269472415017597171/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6838877698951634689657269472415017597171/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (549504263187653735494428953983259606417067/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (549504263187653735494428953983259606417067/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (1096614479103784510667010511776461014190747/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1096614479103784510667010511776461014190747/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2649 BracketBatch0165.bracket2650 (1096614479103784510667010511776461014190747/20000000000000000000000000000000000000000) (5177698509953939666415493030602037574643/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2649 BracketBatch0165.bracket2650
  (1096614479103784510667010511776461014190747/20000000000000000000000000000000000000000) (5177698509953939666415493030602037574643/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2649
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2650
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (68688032898456716936803619247907450802133/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (68688032898456716936803619247907450802133/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (551919403728771348233943261288822147808549/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (551919403728771348233943261288822147808549/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (1101423666916425083728372215272081754225613/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1101423666916425083728372215272081754225613/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2650 BracketBatch0165.bracket2651 (1101423666916425083728372215272081754225613/20000000000000000000000000000000000000000) (5184122520733172569717533086065079874373/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2650 BracketBatch0165.bracket2651
  (1101423666916425083728372215272081754225613/20000000000000000000000000000000000000000) (5184122520733172569717533086065079874373/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2650
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2651
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (275959701864385674116971630644411073904273/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (275959701864385674116971630644411073904273/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (554355917538584194691576358243084548863209/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (554355917538584194691576358243084548863209/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (221255064253471108585103923906381339334351/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (221255064253471108585103923906381339334351/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2651 BracketBatch0165.bracket2652 (221255064253471108585103923906381339334351/4000000000000000000000000000000000000000) (1297643558887094683056928829967005686007/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2651 BracketBatch0165.bracket2652
  (221255064253471108585103923906381339334351/4000000000000000000000000000000000000000) (1297643558887094683056928829967005686007/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2651
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2652
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (277177958769292097345788179121542274431603/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (277177958769292097345788179121542274431603/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (22272563583758186435436340076698691713813/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22272563583758186435436340076698691713813/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (1111170007132538855577484860160551841708531/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1111170007132538855577484860160551841708531/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2652 BracketBatch0165.bracket2653 (1111170007132538855577484860160551841708531/20000000000000000000000000000000000000000) (1039410773148797996724233570442483187159/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2652 BracketBatch0165.bracket2653
  (1111170007132538855577484860160551841708531/20000000000000000000000000000000000000000) (1039410773148797996724233570442483187159/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2652
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2653
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (278407044796977330442954250958733646422661/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (278407044796977330442954250958733646422661/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (279647104980308846057273573796008290995207/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (279647104980308846057273573796008290995207/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (139513537444321544125056956188685484354467/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (139513537444321544125056956188685484354467/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2653 BracketBatch0165.bracket2654 (139513537444321544125056956188685484354467/2500000000000000000000000000000000000000) (1040712323114014320019308273175641400217/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2653 BracketBatch0165.bracket2654
  (139513537444321544125056956188685484354467/2500000000000000000000000000000000000000) (1040712323114014320019308273175641400217/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2653
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2654
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (559294209960617692114547147592016581990411/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (559294209960617692114547147592016581990411/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (561796573907281074543576959110220142748289/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (561796573907281074543576959110220142748289/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (11210907838678987666581241067022367247387/200000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11210907838678987666581241067022367247387/200000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2654 BracketBatch0165.bracket2655 (11210907838678987666581241067022367247387/200000000000000000000000000000000000000) (1042019525005929927035848960834762145757/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2654 BracketBatch0165.bracket2655
  (11210907838678987666581241067022367247387/200000000000000000000000000000000000000) (1042019525005929927035848960834762145757/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2654
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2655
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0414.rows BesselBatch0414.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (280898286953640537271788479555110071374143/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (280898286953640537271788479555110071374143/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (564321482022809508191326130115603056385583/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (564321482022809508191326130115603056385583/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (1126118055930090582734903089225823199133869/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1126118055930090582734903089225823199133869/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0331.rows ScalarLogs0331.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2655 BracketBatch0166.bracket2656 (1126118055930090582734903089225823199133869/20000000000000000000000000000000000000000) (1043332419099821561052827620765176697349/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2655 BracketBatch0166.bracket2656
  (1126118055930090582734903089225823199133869/20000000000000000000000000000000000000000) (1043332419099821561052827620765176697349/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2655
