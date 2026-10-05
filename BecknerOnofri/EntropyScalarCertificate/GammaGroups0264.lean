module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0330
public import BecknerOnofri.EntropyScalarCertificate.Bessel0331
public import BecknerOnofri.EntropyScalarCertificate.Bessel0653
public import BecknerOnofri.EntropyScalarCertificate.Bessel0654
public import BecknerOnofri.EntropyScalarCertificate.Brackets0132
public import BecknerOnofri.EntropyScalarCertificate.Logs0264
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2112
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (69631966515942726872303600098560313863863/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (69631966515942726872303600098560313863863/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (69818875183663622991352851342137986148681/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (69818875183663622991352851342137986148681/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (68091231298635913019363501680028466803/9765625000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (68091231298635913019363501680028466803/9765625000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2112 BracketBatch0132.bracket2113 (68091231298635913019363501680028466803/9765625000000000000000000000000000000) (57272737344914867888385143545076386533/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2112 BracketBatch0132.bracket2113
  (68091231298635913019363501680028466803/9765625000000000000000000000000000000) (57272737344914867888385143545076386533/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2112
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2113
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (34909437591831811495676425671068993074339/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (34909437591831811495676425671068993074339/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (8750851530740402063186313374101976995799/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8750851530740402063186313374101976995799/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0653.rows BesselBatch0653.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (13982568742958683949684335833495380211507/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13982568742958683949684335833495380211507/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2113 BracketBatch0132.bracket2114 (13982568742958683949684335833495380211507/2000000000000000000000000000000000000000) (573591705545026182310764394198687580733/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2113 BracketBatch0132.bracket2114
  (13982568742958683949684335833495380211507/2000000000000000000000000000000000000000) (573591705545026182310764394198687580733/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2113
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2114
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (70006812245923216505490506992815815966389/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (70006812245923216505490506992815815966389/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (70195786200306600328896867308426165968063/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (70195786200306600328896867308426165968063/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (35050649611557454208596843575310495483613/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35050649611557454208596843575310495483613/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2114 BracketBatch0132.bracket2115 (35050649611557454208596843575310495483613/5000000000000000000000000000000000000000) (287229323921853797427335162862647337937/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2114 BracketBatch0132.bracket2115
  (35050649611557454208596843575310495483613/5000000000000000000000000000000000000000) (287229323921853797427335162862647337937/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2114
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2115
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (3509789310015330016444843365421308298403/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3509789310015330016444843365421308298403/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (17596451409574710566422145670254326520633/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17596451409574710566422145670254326520633/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (4393174744956420081080795312170108501581/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4393174744956420081080795312170108501581/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2115 BracketBatch0132.bracket2116 (4393174744956420081080795312170108501581/625000000000000000000000000000000000000) (1150656430112488058547089426981582331061/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2115 BracketBatch0132.bracket2116
  (4393174744956420081080795312170108501581/625000000000000000000000000000000000000) (1150656430112488058547089426981582331061/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2115
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2116
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (70385805638298842265688582681017306082529/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (70385805638298842265688582681017306082529/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (70576879246585516894595184137949975510359/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (70576879246585516894595184137949975510359/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (17620335610610544895035470852370910199111/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17620335610610544895035470852370910199111/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2116 BracketBatch0132.bracket2117 (17620335610610544895035470852370910199111/2500000000000000000000000000000000000000) (1152400844035360183672230787613384502253/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2116 BracketBatch0132.bracket2117
  (17620335610610544895035470852370910199111/2500000000000000000000000000000000000000) (1152400844035360183672230787613384502253/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2116
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2117
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (17644219811646379223648796034487493877589/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17644219811646379223648796034487493877589/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (8846126976046864148535419406035368603129/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8846126976046864148535419406035368603129/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (35336473763740107520719634846558231083847/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35336473763740107520719634846558231083847/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2117 BracketBatch0132.bracket2118 (35336473763740107520719634846558231083847/5000000000000000000000000000000000000000) (1154150567376838244688878656825824176871/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2117 BracketBatch0132.bracket2118
  (35336473763740107520719634846558231083847/5000000000000000000000000000000000000000) (1154150567376838244688878656825824176871/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2117
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2118
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0330.rows BesselBatch0330.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (70769015808374913188283355248282948825029/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (70769015808374913188283355248282948825029/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (35481112102371170256029547101733580357709/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (35481112102371170256029547101733580357709/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (141731240013117253700342449451750109540447/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (141731240013117253700342449451750109540447/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2118 BracketBatch0132.bracket2119 (141731240013117253700342449451750109540447/20000000000000000000000000000000000000000) (231181126062242778878830851430316678773/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2118 BracketBatch0132.bracket2119
  (141731240013117253700342449451750109540447/20000000000000000000000000000000000000000) (231181126062242778878830851430316678773/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2118
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2119
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (14192444840948468102411818840693432143083/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14192444840948468102411818840693432143083/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0331.rows BesselBatch0331.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (71156513415996965091240515175670344917789/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (71156513415996965091240515175670344917789/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0654.rows BesselBatch0654.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (35529684405184826400824902344784376408301/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35529684405184826400824902344784376408301/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0264.rows ScalarLogs0264.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0132.bracket2119 BracketBatch0132.bracket2120 (35529684405184826400824902344784376408301/5000000000000000000000000000000000000000) (578833031634534443063955010995419232349/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0132.bracket2119 BracketBatch0132.bracket2120
  (35529684405184826400824902344784376408301/5000000000000000000000000000000000000000) (578833031634534443063955010995419232349/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2119
