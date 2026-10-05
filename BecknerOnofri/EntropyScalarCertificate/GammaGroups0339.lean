module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0423
public import BecknerOnofri.EntropyScalarCertificate.Bessel0424
public import BecknerOnofri.EntropyScalarCertificate.Bessel0425
public import BecknerOnofri.EntropyScalarCertificate.Bessel0700
public import BecknerOnofri.EntropyScalarCertificate.Bessel0701
public import BecknerOnofri.EntropyScalarCertificate.Brackets0169
public import BecknerOnofri.EntropyScalarCertificate.Brackets0170
public import BecknerOnofri.EntropyScalarCertificate.Logs0339
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2712
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (47141770344097730226156449977888347052631/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (47141770344097730226156449977888347052631/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (758831996756269311072678391245001140668293/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (758831996756269311072678391245001140668293/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (1513100322261832994691181590891214693510389/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1513100322261832994691181590891214693510389/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2712 BracketBatch0169.bracket2713 (1513100322261832994691181590891214693510389/20000000000000000000000000000000000000000) (2823080330717603575272337774463171222481/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2712 BracketBatch0169.bracket2713
  (1513100322261832994691181590891214693510389/20000000000000000000000000000000000000000) (2823080330717603575272337774463171222481/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2712
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2713
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (75883199675626931107267839124500114066829/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (75883199675626931107267839124500114066829/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (763451323003342373362320780207104418929593/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (763451323003342373362320780207104418929593/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (1522283319759611684434999171452105559597883/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1522283319759611684434999171452105559597883/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2713 BracketBatch0169.bracket2714 (1522283319759611684434999171452105559597883/20000000000000000000000000000000000000000) (565482805123446884203981051819035989733/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2713 BracketBatch0169.bracket2714
  (1522283319759611684434999171452105559597883/20000000000000000000000000000000000000000) (565482805123446884203981051819035989733/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2713
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2714
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (76345132300334237336232078020710441892959/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (76345132300334237336232078020710441892959/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (96015916071474608324282544405997073921147/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (96015916071474608324282544405997073921147/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0700.rows BesselBatch0700.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (765789325787569619978290567727540505149383/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (765789325787569619978290567727540505149383/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2714 BracketBatch0169.bracket2715 (765789325787569619978290567727540505149383/10000000000000000000000000000000000000000) (5663540587401808707621050507179337211369/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2714 BracketBatch0169.bracket2715
  (765789325787569619978290567727540505149383/10000000000000000000000000000000000000000) (5663540587401808707621050507179337211369/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2714
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2715
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (768127328571796866594260355247976591369173/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (768127328571796866594260355247976591369173/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (6182888504628979707393113860450374069531/80000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6182888504628979707393113860450374069531/80000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (385247097912604832504599896951068337515137/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (385247097912604832504599896951068337515137/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2715 BracketBatch0169.bracket2716 (385247097912604832504599896951068337515137/5000000000000000000000000000000000000000) (5672298593340759743036265468593608149663/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2715 BracketBatch0169.bracket2716
  (385247097912604832504599896951068337515137/5000000000000000000000000000000000000000) (5672298593340759743036265468593608149663/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2715
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2716
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (193215265769655615856034808139074189672843/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (193215265769655615856034808139074189672843/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (777653602218249596167514422506643063646633/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (777653602218249596167514422506643063646633/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (310102933059374411918330731012587964467601/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (310102933059374411918330731012587964467601/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2716 BracketBatch0169.bracket2717 (310102933059374411918330731012587964467601/4000000000000000000000000000000000000000) (5681102391468082953994449468965416244521/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2716 BracketBatch0169.bracket2717
  (310102933059374411918330731012587964467601/4000000000000000000000000000000000000000) (5681102391468082953994449468965416244521/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2716
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2717
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (77765360221824959616751442250664306364663/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (77765360221824959616751442250664306364663/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (156501209715493896105527168829097085304339/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (156501209715493896105527168829097085304339/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (62406386031828763067806010666085139606733/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (62406386031828763067806010666085139606733/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2717 BracketBatch0169.bracket2718 (62406386031828763067806010666085139606733/800000000000000000000000000000000000000) (1137990460586790953704063881098317071129/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2717 BracketBatch0169.bracket2718
  (62406386031828763067806010666085139606733/800000000000000000000000000000000000000) (1137990460586790953704063881098317071129/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2717
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2718
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (195626512144367370131908961036371356630423/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (195626512144367370131908961036371356630423/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (393709766240552919165914338455717234582627/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (393709766240552919165914338455717234582627/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (784962790529287659429732260528459947843473/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (784962790529287659429732260528459947843473/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2718 BracketBatch0169.bracket2719 (784962790529287659429732260528459947843473/10000000000000000000000000000000000000000) (2849424323661189245575826211612851931661/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2718 BracketBatch0169.bracket2719
  (784962790529287659429732260528459947843473/10000000000000000000000000000000000000000) (2849424323661189245575826211612851931661/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2718
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2719
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (787419532481105838331828676911434469165251/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (787419532481105838331828676911434469165251/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0425.rows BesselBatch0425.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (396197606434900368160582521163940877520951/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (396197606434900368160582521163940877520951/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0701.rows BesselBatch0701.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (1579814745350906574652993719239316224207153/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1579814745350906574652993719239316224207153/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0339.rows ScalarLogs0339.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0169.bracket2719 BracketBatch0170.bracket2720 (1579814745350906574652993719239316224207153/20000000000000000000000000000000000000000) (2853895871165261372555854288893313626983/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0169.bracket2719 BracketBatch0170.bracket2720
  (1579814745350906574652993719239316224207153/20000000000000000000000000000000000000000) (2853895871165261372555854288893313626983/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2719
