module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0070
public import BecknerOnofri.EntropyScalarCertificate.Bessel0071
public import BecknerOnofri.EntropyScalarCertificate.Bessel0523
public import BecknerOnofri.EntropyScalarCertificate.Bessel0524
public import BecknerOnofri.EntropyScalarCertificate.Brackets0028
public import BecknerOnofri.EntropyScalarCertificate.Logs0056
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0448
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (7384378903900070359908231049669956029/50000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7384378903900070359908231049669956029/50000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (739470931686333516548695685883222417987/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (739470931686333516548695685883222417987/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (1477908822076340552539518790850218020887/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1477908822076340552539518790850218020887/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0448 BracketBatch0028.bracket0449 (1477908822076340552539518790850218020887/10000000000000000000000000000000000000000) (357606740821922080006132617075633947/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0448 BracketBatch0028.bracket0449
  (1477908822076340552539518790850218020887/10000000000000000000000000000000000000000) (357606740821922080006132617075633947/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0448
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0449
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (1478941863372667033097391371766444835971/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1478941863372667033097391371766444835971/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (1481008132425880429814647265961845913033/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1481008132425880429814647265961845913033/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (739987498949636865728009659432072687251/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (739987498949636865728009659432072687251/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0449 BracketBatch0028.bracket0450 (739987498949636865728009659432072687251/5000000000000000000000000000000000000000) (44947471571385570745811013100941247/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0449 BracketBatch0028.bracket0450
  (739987498949636865728009659432072687251/5000000000000000000000000000000000000000) (44947471571385570745811013100941247/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0449
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0450
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (148100813242588042981464726596184591303/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (148100813242588042981464726596184591303/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1483074588225739842286703747422302163721/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1483074588225739842286703747422302163721/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (2964082720651620272101351013384148076751/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2964082720651620272101351013384148076751/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0450 BracketBatch0028.bracket0451 (2964082720651620272101351013384148076751/20000000000000000000000000000000000000000) (361560984002418690634945858576422549/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0450 BracketBatch0028.bracket0451
  (2964082720651620272101351013384148076751/20000000000000000000000000000000000000000) (361560984002418690634945858576422549/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0450
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0451
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (741537294112869921143351873711151081859/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (741537294112869921143351873711151081859/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (1485141231058466153876952221203234880533/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1485141231058466153876952221203234880533/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (2968215819284205996163655968625537044251/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2968215819284205996163655968625537044251/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0451 BracketBatch0028.bracket0452 (2968215819284205996163655968625537044251/20000000000000000000000000000000000000000) (363550397988611163406426646089999087/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0451 BracketBatch0028.bracket0452
  (2968215819284205996163655968625537044251/20000000000000000000000000000000000000000) (363550397988611163406426646089999087/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0451
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0452
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (148514123105846615387695222120323488053/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (148514123105846615387695222120323488053/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (371802015302603947351479183107949342087/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (371802015302603947351479183107949342087/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (1486174646134440971641434476817516124439/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1486174646134440971641434476817516124439/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0452 BracketBatch0028.bracket0453 (1486174646134440971641434476817516124439/10000000000000000000000000000000000000000) (365548037436353932409003864276251853/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0452 BracketBatch0028.bracket0453
  (1486174646134440971641434476817516124439/10000000000000000000000000000000000000000) (365548037436353932409003864276251853/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0452
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0453
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (297441612242083157881183346486359473669/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (297441612242083157881183346486359473669/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1489275078968080953640586172162549133429/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1489275078968080953640586172162549133429/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (1488241570089248371523251452297173250887/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1488241570089248371523251452297173250887/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0453 BracketBatch0028.bracket0454 (1488241570089248371523251452297173250887/10000000000000000000000000000000000000000) (459442406607945026921142056887263/12500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0453 BracketBatch0028.bracket0454
  (1488241570089248371523251452297173250887/10000000000000000000000000000000000000000) (459442406607945026921142056887263/12500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0453
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0454
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0070.rows BesselBatch0070.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (744637539484040476820293086081274566713/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (744637539484040476820293086081274566713/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (186417785577261233753318428225856110159/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (186417785577261233753318428225856110159/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (1490308681793085411833566798984699007349/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1490308681793085411833566798984699007349/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0454 BracketBatch0028.bracket0455 (1490308681793085411833566798984699007349/10000000000000000000000000000000000000000) (369568084513355387503823397602477093/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0454 BracketBatch0028.bracket0455
  (1490308681793085411833566798984699007349/10000000000000000000000000000000000000000) (369568084513355387503823397602477093/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0454
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0455
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (1491342284618089870026547425806848881269/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1491342284618089870026547425806848881269/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0071.rows BesselBatch0071.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (298681935689441403932684019529806912851/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (298681935689441403932684019529806912851/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0524.rows BesselBatch0524.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (746187990766324222422491880863970861381/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (746187990766324222422491880863970861381/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0056.rows ScalarLogs0056.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0028.bracket0455 BracketBatch0028.bracket0456 (746187990766324222422491880863970861381/5000000000000000000000000000000000000000) (9289763453153269923347231208364599/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0028.bracket0455 BracketBatch0028.bracket0456
  (746187990766324222422491880863970861381/5000000000000000000000000000000000000000) (9289763453153269923347231208364599/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0455
