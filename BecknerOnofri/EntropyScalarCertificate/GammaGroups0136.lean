module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0170
public import BecknerOnofri.EntropyScalarCertificate.Bessel0171
public import BecknerOnofri.EntropyScalarCertificate.Bessel0573
public import BecknerOnofri.EntropyScalarCertificate.Bessel0574
public import BecknerOnofri.EntropyScalarCertificate.Brackets0068
public import BecknerOnofri.EntropyScalarCertificate.Logs0136
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1088
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (874011540452193414087517973021124046127/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (874011540452193414087517973021124046127/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (7010810949215879207479506510794194447491/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7010810949215879207479506510794194447491/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (14002903272833426520179650294963186816507/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14002903272833426520179650294963186816507/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1088 BracketBatch0068.bracket1089 (14002903272833426520179650294963186816507/20000000000000000000000000000000000000000) (96067069728154457102299811308296598539/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1088 BracketBatch0068.bracket1089
  (14002903272833426520179650294963186816507/20000000000000000000000000000000000000000) (96067069728154457102299811308296598539/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1088
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1089
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (54771960540749056308433644615579644121/78125000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (54771960540749056308433644615579644121/78125000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (351479171617899166380755600539554283223/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (351479171617899166380755600539554283223/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0573.rows BesselBatch0573.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (3510098595393465633773654630396320027987/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3510098595393465633773654630396320027987/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1089 BracketBatch0068.bracket1090 (3510098595393465633773654630396320027987/5000000000000000000000000000000000000000) (6050545934062376163939701110459290621/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1089 BracketBatch0068.bracket1090
  (3510098595393465633773654630396320027987/5000000000000000000000000000000000000000) (6050545934062376163939701110459290621/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1089
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1090
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (7029583432357983327615112010791085664457/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7029583432357983327615112010791085664457/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (352420507306960781586096526583063777189/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (352420507306960781586096526583063777189/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (14077993578497198959337042542452361208237/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14077993578497198959337042542452361208237/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1090 BracketBatch0068.bracket1091 (14077993578497198959337042542452361208237/20000000000000000000000000000000000000000) (97555170351005710715351973947507229097/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1090 BracketBatch0068.bracket1091
  (14077993578497198959337042542452361208237/20000000000000000000000000000000000000000) (97555170351005710715351973947507229097/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1090
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1091
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (7048410146139215631721930531661275543777/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7048410146139215631721930531661275543777/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (7067291467155085231440139509082415847401/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7067291467155085231440139509082415847401/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (7057850806647150431581035020371845695589/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7057850806647150431581035020371845695589/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1091 BracketBatch0068.bracket1092 (7057850806647150431581035020371845695589/10000000000000000000000000000000000000000) (98306403520325122181876496167454669533/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1091 BracketBatch0068.bracket1092
  (7057850806647150431581035020371845695589/10000000000000000000000000000000000000000) (98306403520325122181876496167454669533/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1091
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1092
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (3533645733577542615720069754541207923699/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3533645733577542615720069754541207923699/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (3543113887772086079965389761466763830023/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3543113887772086079965389761466763830023/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (3538379810674814347842729758003985876861/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3538379810674814347842729758003985876861/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1092 BracketBatch0068.bracket1093 (3538379810674814347842729758003985876861/5000000000000000000000000000000000000000) (99062462213471465192126003914001540281/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1092 BracketBatch0068.bracket1093
  (3538379810674814347842729758003985876861/5000000000000000000000000000000000000000) (99062462213471465192126003914001540281/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1092
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1093
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (7086227775544172159930779522933527660043/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7086227775544172159930779522933527660043/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (35526097275158420043334281882184319319/50000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (35526097275158420043334281882184319319/50000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (14191447230575856168597635899370391523843/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14191447230575856168597635899370391523843/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1093 BracketBatch0068.bracket1094 (14191447230575856168597635899370391523843/20000000000000000000000000000000000000000) (99823374379240349774599914904599364333/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1093 BracketBatch0068.bracket1094
  (14191447230575856168597635899370391523843/20000000000000000000000000000000000000000) (99823374379240349774599914904599364333/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1093
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1094
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0170.rows BesselBatch0170.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (7105219455031684008666856376436863863797/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7105219455031684008666856376436863863797/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (7124266892973662598401144957590684591583/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7124266892973662598401144957590684591583/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (711474317400267330353400066701377422769/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (711474317400267330353400066701377422769/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1094 BracketBatch0068.bracket1095 (711474317400267330353400066701377422769/1000000000000000000000000000000000000000) (100589168156647408159344068112932353741/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1094 BracketBatch0068.bracket1095
  (711474317400267330353400066701377422769/1000000000000000000000000000000000000000) (100589168156647408159344068112932353741/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1094
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1095
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (356213344648683129920057247879534229579/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (356213344648683129920057247879534229579/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0171.rows BesselBatch0171.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (7143370480401852073297796073438910603863/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7143370480401852073297796073438910603863/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0574.rows BesselBatch0574.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (14267637373375514671698941031029595195443/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14267637373375514671698941031029595195443/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0136.rows ScalarLogs0136.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0068.bracket1095 BracketBatch0068.bracket1096 (14267637373375514671698941031029595195443/20000000000000000000000000000000000000000) (50679935938447608553791795999394428673/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0068.bracket1095 BracketBatch0068.bracket1096
  (14267637373375514671698941031029595195443/20000000000000000000000000000000000000000) (50679935938447608553791795999394428673/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1095
