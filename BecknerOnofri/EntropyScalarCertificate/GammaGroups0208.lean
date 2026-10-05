module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0260
public import BecknerOnofri.EntropyScalarCertificate.Bessel0261
public import BecknerOnofri.EntropyScalarCertificate.Bessel0618
public import BecknerOnofri.EntropyScalarCertificate.Bessel0619
public import BecknerOnofri.EntropyScalarCertificate.Brackets0104
public import BecknerOnofri.EntropyScalarCertificate.Logs0208
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1664
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (19382476658693208080838518020112953553133/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19382476658693208080838518020112953553133/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (3878917360488156131550416737952142437197/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3878917360488156131550416737952142437197/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (19388531730566994369295300854936832869559/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19388531730566994369295300854936832869559/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1664 BracketBatch0104.bracket1665 (19388531730566994369295300854936832869559/10000000000000000000000000000000000000000) (384803764437029227322134372409467714679/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1664 BracketBatch0104.bracket1665
  (19388531730566994369295300854936832869559/10000000000000000000000000000000000000000) (384803764437029227322134372409467714679/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1664
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1665
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (9697293401220390328876041844880356092991/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9697293401220390328876041844880356092991/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (19406714332807404751694986437138856279757/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19406714332807404751694986437138856279757/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0618.rows BesselBatch0618.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (38801301135248185409447070126899568465739/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38801301135248185409447070126899568465739/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1665 BracketBatch0104.bracket1666 (38801301135248185409447070126899568465739/20000000000000000000000000000000000000000) (154047393002809075052282274868315792689/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1665 BracketBatch0104.bracket1666
  (38801301135248185409447070126899568465739/20000000000000000000000000000000000000000) (154047393002809075052282274868315792689/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1665
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1666
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (9703357166403702375847493218569428139877/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9703357166403702375847493218569428139877/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (3883771857726443272937383923225075260733/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3883771857726443272937383923225075260733/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (38825573621439621116381906053264232583419/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38825573621439621116381906053264232583419/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1666 BracketBatch0104.bracket1667 (38825573621439621116381906053264232583419/20000000000000000000000000000000000000000) (770867106628865804314523975569436062877/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1666 BracketBatch0104.bracket1667
  (38825573621439621116381906053264232583419/20000000000000000000000000000000000000000) (770867106628865804314523975569436062877/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1666
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1667
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (9709429644316108182343459808062688151831/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9709429644316108182343459808062688151831/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (19431021708864565338657498035772162919549/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19431021708864565338657498035772162919549/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (38849880997496781703344417651897539223211/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38849880997496781703344417651897539223211/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1667 BracketBatch0104.bracket1668 (38849880997496781703344417651897539223211/20000000000000000000000000000000000000000) (771497954846964468773390096737255331669/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1667 BracketBatch0104.bracket1668
  (38849880997496781703344417651897539223211/20000000000000000000000000000000000000000) (771497954846964468773390096737255331669/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1667
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1668
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (9715510854432282669328749017886081459773/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9715510854432282669328749017886081459773/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (19443201632564392154359076489836776681087/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19443201632564392154359076489836776681087/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (38874223341428957493016574525608939600633/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38874223341428957493016574525608939600633/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1668 BracketBatch0104.bracket1669 (38874223341428957493016574525608939600633/20000000000000000000000000000000000000000) (772129510798946360929664891714993392419/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1668 BracketBatch0104.bracket1669
  (38874223341428957493016574525608939600633/20000000000000000000000000000000000000000) (772129510798946360929664891714993392419/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1668
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1669
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (4860800408141098038589769122459194170271/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4860800408141098038589769122459194170271/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (2431924887362825784354181168656537455971/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2431924887362825784354181168656537455971/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (9724650182866749607298131459772269082213/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9724650182866749607298131459772269082213/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1669 BracketBatch0104.bracket1670 (9724650182866749607298131459772269082213/5000000000000000000000000000000000000000) (77276177561758127442498795822758820731/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1669 BracketBatch0104.bracket1670
  (9724650182866749607298131459772269082213/5000000000000000000000000000000000000000) (77276177561758127442498795822758820731/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1669
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1670
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0260.rows BesselBatch0260.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (3891079819780521254966689869850459929553/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3891079819780521254966689869850459929553/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (19467614147161466041104843256746144157479/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19467614147161466041104843256746144157479/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (9730753311516018078984573151499610951311/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9730753311516018078984573151499610951311/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1670 BracketBatch0104.bracket1671 (9730753311516018078984573151499610951311/5000000000000000000000000000000000000000) (386697375218904176727643557633232021447/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1670 BracketBatch0104.bracket1671
  (9730753311516018078984573151499610951311/5000000000000000000000000000000000000000) (386697375218904176727643557633232021447/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1670
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1671
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (4866903536790366510276210814186536039369/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4866903536790366510276210814186536039369/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (19479846816734960127817259257642677408989/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19479846816734960127817259257642677408989/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (7789492192779285233784420502877764313293/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7789492192779285233784420502877764313293/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0208.rows ScalarLogs0208.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1671 BracketBatch0104.bracket1672 (7789492192779285233784420502877764313293/4000000000000000000000000000000000000000) (774028436396740655227152864651038421273/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1671 BracketBatch0104.bracket1672
  (7789492192779285233784420502877764313293/4000000000000000000000000000000000000000) (774028436396740655227152864651038421273/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1671
