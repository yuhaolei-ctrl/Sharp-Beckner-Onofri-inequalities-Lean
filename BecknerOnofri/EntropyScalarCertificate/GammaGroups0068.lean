module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0085
public import BecknerOnofri.EntropyScalarCertificate.Bessel0086
public import BecknerOnofri.EntropyScalarCertificate.Bessel0531
public import BecknerOnofri.EntropyScalarCertificate.Bessel0532
public import BecknerOnofri.EntropyScalarCertificate.Brackets0034
public import BecknerOnofri.EntropyScalarCertificate.Logs0068
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0544
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (838055655001573767446939757579778955267/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (838055655001573767446939757579778955267/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (335639323499740250823670149624138787639/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (335639323499740250823670149624138787639/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (3354307927501848789012230263280251848729/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3354307927501848789012230263280251848729/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0544 BracketBatch0034.bracket0545 (3354307927501848789012230263280251848729/20000000000000000000000000000000000000000) (293847585696100810582558451947891367/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0544 BracketBatch0034.bracket0545
  (3354307927501848789012230263280251848729/20000000000000000000000000000000000000000) (293847585696100810582558451947891367/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0544
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0545
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (104887288593668828382396921757543371137/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (104887288593668828382396921757543371137/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (210035267446361339435098432065611670841/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (210035267446361339435098432065611670841/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (83961968926739799239978455116139682623/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (83961968926739799239978455116139682623/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0545 BracketBatch0034.bracket0546 (83961968926739799239978455116139682623/500000000000000000000000000000000000000) (590562591798626425046933612017992761/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0545 BracketBatch0034.bracket0546
  (83961968926739799239978455116139682623/500000000000000000000000000000000000000) (590562591798626425046933612017992761/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0545
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0546
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (67211285582835628619231498260995734669/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (67211285582835628619231498260995734669/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1682367876519913345338664105885962393357/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1682367876519913345338664105885962393357/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (1681325008045402030409725781205427880041/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1681325008045402030409725781205427880041/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0546 BracketBatch0034.bracket0547 (1681325008045402030409725781205427880041/10000000000000000000000000000000000000000) (18545017002722196513180999452287383/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0546 BracketBatch0034.bracket0547
  (1681325008045402030409725781205427880041/10000000000000000000000000000000000000000) (18545017002722196513180999452287383/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0546
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0547
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (841183938259956672669332052942981196677/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (841183938259956672669332052942981196677/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (1684453828646125924086924205278507174391/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1684453828646125924086924205278507174391/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (673364341033207853885117662232893913549/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (673364341033207853885117662232893913549/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0547 BracketBatch0034.bracket0548 (673364341033207853885117662232893913549/4000000000000000000000000000000000000000) (596329054450144670441800336698355129/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0547 BracketBatch0034.bracket0548
  (673364341033207853885117662232893913549/4000000000000000000000000000000000000000) (596329054450144670441800336698355129/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0547
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0548
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (421113457161531481021731051319626793597/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (421113457161531481021731051319626793597/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (1686539996250044850067184665262739243763/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1686539996250044850067184665262739243763/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (3370993824896170774154108870541246418151/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3370993824896170774154108870541246418151/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0548 BracketBatch0034.bracket0549 (3370993824896170774154108870541246418151/20000000000000000000000000000000000000000) (599228149115452894845565077617996029/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0548 BracketBatch0034.bracket0549
  (3370993824896170774154108870541246418151/20000000000000000000000000000000000000000) (599228149115452894845565077617996029/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0548
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0549
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (21081749953125560625839808315784240547/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21081749953125560625839808315784240547/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (67545055185293856150847937516171555117/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (67545055185293856150847937516171555117/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (675033275176478250767676620633405624337/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (675033275176478250767676620633405624337/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0549 BracketBatch0034.bracket0550 (675033275176478250767676620633405624337/4000000000000000000000000000000000000000) (602137854346003989312247195301564047/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0549 BracketBatch0034.bracket0550
  (675033275176478250767676620633405624337/4000000000000000000000000000000000000000) (602137854346003989312247195301564047/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0549
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0550
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0085.rows BesselBatch0085.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (844313189816173201885599218952144438961/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (844313189816173201885599218952144438961/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (1690712979093867012339162299900767820809/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1690712979093867012339162299900767820809/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (3379339358726213416110360737805056698731/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3379339358726213416110360737805056698731/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0550 BracketBatch0034.bracket0551 (3379339358726213416110360737805056698731/20000000000000000000000000000000000000000) (302529098220013273341530953781830677/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0550 BracketBatch0034.bracket0551
  (3379339358726213416110360737805056698731/20000000000000000000000000000000000000000) (302529098220013273341530953781830677/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0550
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0551
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (845356489546933506169581149950383910403/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (845356489546933506169581149950383910403/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0086.rows BesselBatch0086.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (846399897467801757176728827961330923743/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (846399897467801757176728827961330923743/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0531.rows BesselBatch0531.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0532.rows BesselBatch0532.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (845878193507367631673154988955857417073/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (845878193507367631673154988955857417073/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0068.rows ScalarLogs0068.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0034.bracket0551 BracketBatch0034.bracket0552 (845878193507367631673154988955857417073/5000000000000000000000000000000000000000) (151997300432755652017878832784920891/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0034.bracket0551 BracketBatch0034.bracket0552
  (845878193507367631673154988955857417073/5000000000000000000000000000000000000000) (151997300432755652017878832784920891/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0551
