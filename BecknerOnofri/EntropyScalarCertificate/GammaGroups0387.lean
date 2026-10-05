module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0483
public import BecknerOnofri.EntropyScalarCertificate.Bessel0484
public import BecknerOnofri.EntropyScalarCertificate.Bessel0485
public import BecknerOnofri.EntropyScalarCertificate.Bessel0730
public import BecknerOnofri.EntropyScalarCertificate.Bessel0731
public import BecknerOnofri.EntropyScalarCertificate.Brackets0193
public import BecknerOnofri.EntropyScalarCertificate.Brackets0194
public import BecknerOnofri.EntropyScalarCertificate.Logs0387
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3096
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (2156424595127831238085633558766909244901631/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2156424595127831238085633558766909244901631/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (216575433640728324292890822931570281931139/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (216575433640728324292890822931570281931139/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (4322178931535114481014541788082612064213021/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4322178931535114481014541788082612064213021/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3096 BracketBatch0193.bracket3097 (4322178931535114481014541788082612064213021/20000000000000000000000000000000000000000) (7284685905465023414420448360020178651047/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3096 BracketBatch0193.bracket3097
  (4322178931535114481014541788082612064213021/20000000000000000000000000000000000000000) (7284685905465023414420448360020178651047/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3096
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3097
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0483.rows BesselBatch0483.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (2165754336407283242928908229315702819311387/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2165754336407283242928908229315702819311387/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (108758260297700398786632949767397972302707/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (108758260297700398786632949767397972302707/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (4340919542361291218661567224663662265365527/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4340919542361291218661567224663662265365527/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3097 BracketBatch0193.bracket3098 (4340919542361291218661567224663662265365527/20000000000000000000000000000000000000000) (1822761160035786869879101280251337177133/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3097 BracketBatch0193.bracket3098
  (4340919542361291218661567224663662265365527/20000000000000000000000000000000000000000) (1822761160035786869879101280251337177133/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3097
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3098
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (2175165205954007975732658995347959446054137/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2175165205954007975732658995347959446054137/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1092329133291865388320066048241707375809121/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1092329133291865388320066048241707375809121/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (4359823472537738752372791091831374197672379/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4359823472537738752372791091831374197672379/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3098 BracketBatch0193.bracket3099 (4359823472537738752372791091831374197672379/20000000000000000000000000000000000000000) (7297425644818683010972595199892214134677/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3098 BracketBatch0193.bracket3099
  (4359823472537738752372791091831374197672379/20000000000000000000000000000000000000000) (7297425644818683010972595199892214134677/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3098
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3099
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (2184658266583730776640132096483414751618239/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2184658266583730776640132096483414751618239/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (2194234599758066904277519323862748838982217/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2194234599758066904277519323862748838982217/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (547361608292724710114706427543270448825057/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (547361608292724710114706427543270448825057/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3099 BracketBatch0193.bracket3100 (547361608292724710114706427543270448825057/2500000000000000000000000000000000000000) (1825957253501375423110399406748905281271/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3099 BracketBatch0193.bracket3100
  (547361608292724710114706427543270448825057/2500000000000000000000000000000000000000) (1825957253501375423110399406748905281271/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3099
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3100
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (1097117299879033452138759661931374419491107/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1097117299879033452138759661931374419491107/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (110194765299761197843294384331235933394411/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (110194765299761197843294384331235933394411/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (2199064952876645430571703505243733753435217/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2199064952876645430571703505243733753435217/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3100 BracketBatch0193.bracket3101 (2199064952876645430571703505243733753435217/10000000000000000000000000000000000000000) (3655127420650686753932448950669196561923/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3100 BracketBatch0193.bracket3101
  (2199064952876645430571703505243733753435217/10000000000000000000000000000000000000000) (3655127420650686753932448950669196561923/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3100
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3101
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (2203895305995223956865887686624718667888217/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2203895305995223956865887686624718667888217/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (55341037632290197435835645017474870956097/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (55341037632290197435835645017474870956097/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (4417536811286831854299313487323713506132097/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4417536811286831854299313487323713506132097/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3101 BracketBatch0193.bracket3102 (4417536811286831854299313487323713506132097/20000000000000000000000000000000000000000) (7316703219315408373774859923210024506871/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3101 BracketBatch0193.bracket3102
  (4417536811286831854299313487323713506132097/20000000000000000000000000000000000000000) (7316703219315408373774859923210024506871/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3101
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3102
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (2213641505291607897433425800698994838243877/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2213641505291607897433425800698994838243877/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (1778779470043737525093346816130485258449/8000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1778779470043737525093346816130485258449/8000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (4437115842846279803800109320862101411305127/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4437115842846279803800109320862101411305127/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3102 BracketBatch0193.bracket3103 (4437115842846279803800109320862101411305127/20000000000000000000000000000000000000000) (91539677994901982131580414747848356463/125000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3102 BracketBatch0193.bracket3103
  (4437115842846279803800109320862101411305127/20000000000000000000000000000000000000000) (91539677994901982131580414747848356463/125000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3102
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3103
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0484.rows BesselBatch0484.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (2223474337554671906366683520163106573061247/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2223474337554671906366683520163106573061247/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0485.rows BesselBatch0485.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (2233394963047359399655148349992199311849921/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2233394963047359399655148349992199311849921/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0731.rows BesselBatch0731.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (69638582821906739156591122971176654451737/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (69638582821906739156591122971176654451737/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0387.rows ScalarLogs0387.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0193.bracket3103 BracketBatch0194.bracket3104 (69638582821906739156591122971176654451737/312500000000000000000000000000000000000) (183241699813305789071742619585394223707/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0193.bracket3103 BracketBatch0194.bracket3104
  (69638582821906739156591122971176654451737/312500000000000000000000000000000000000) (183241699813305789071742619585394223707/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3103
