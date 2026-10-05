module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0310
public import BecknerOnofri.EntropyScalarCertificate.Bessel0311
public import BecknerOnofri.EntropyScalarCertificate.Bessel0643
public import BecknerOnofri.EntropyScalarCertificate.Bessel0644
public import BecknerOnofri.EntropyScalarCertificate.Brackets0124
public import BecknerOnofri.EntropyScalarCertificate.Logs0248
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1984
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (51964206099547817539626417078031542337157/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (51964206099547817539626417078031542337157/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (52066604278131229889029181455531995395419/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (52066604278131229889029181455531995395419/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (3250962824302470232145487454173860554143/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3250962824302470232145487454173860554143/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1984 BracketBatch0124.bracket1985 (3250962824302470232145487454173860554143/625000000000000000000000000000000000000) (479489349429717773487931098580763810591/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1984 BracketBatch0124.bracket1985
  (3250962824302470232145487454173860554143/625000000000000000000000000000000000000) (479489349429717773487931098580763810591/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1984
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1985
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (6508325534766403736128647681941499424427/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6508325534766403736128647681941499424427/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (652117749258185405337502560621982551261/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (652117749258185405337502560621982551261/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0643.rows BesselBatch0643.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (13029503027348257789503673288161324937037/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13029503027348257789503673288161324937037/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1985 BracketBatch0124.bracket1986 (13029503027348257789503673288161324937037/2500000000000000000000000000000000000000) (38408692492665296240476570178559899267/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1985 BracketBatch0124.bracket1986
  (13029503027348257789503673288161324937037/2500000000000000000000000000000000000000) (38408692492665296240476570178559899267/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1985
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1986
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (52169419940654832427000204849758604100877/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (52169419940654832427000204849758604100877/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (52272655636226404516376239860074529589303/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (52272655636226404516376239860074529589303/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (5222103778844061847168822235491656684509/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5222103778844061847168822235491656684509/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1986 BracketBatch0124.bracket1987 (5222103778844061847168822235491656684509/1000000000000000000000000000000000000000) (1922917515959517861463936467668777537877/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1986 BracketBatch0124.bracket1987
  (5222103778844061847168822235491656684509/1000000000000000000000000000000000000000) (1922917515959517861463936467668777537877/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1986
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1987
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (522726556362264045163762398600745295893/100000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (522726556362264045163762398600745295893/100000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (52376313934769069329854885093093176759197/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (52376313934769069329854885093093176759197/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (104648969570995473846231124953167706348497/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (104648969570995473846231124953167706348497/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1987 BracketBatch0124.bracket1988 (104648969570995473846231124953167706348497/20000000000000000000000000000000000000000) (1925406095026040833355976302424544531707/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1987 BracketBatch0124.bracket1988
  (104648969570995473846231124953167706348497/20000000000000000000000000000000000000000) (1925406095026040833355976302424544531707/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1987
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1988
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (26188156967384534664927442546546588379597/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26188156967384534664927442546546588379597/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (52480397427234098654387519303409724350189/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (52480397427234098654387519303409724350189/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (104856711362003167984242404396502901109383/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (104856711362003167984242404396502901109383/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1988 BracketBatch0124.bracket1989 (104856711362003167984242404396502901109383/20000000000000000000000000000000000000000) (1927900385309400820480048487199602161229/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1988 BracketBatch0124.bracket1989
  (104856711362003167984242404396502901109383/20000000000000000000000000000000000000000) (1927900385309400820480048487199602161229/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1988
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1989
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (26240198713617049327193759651704862175093/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26240198713617049327193759651704862175093/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (26292454362908167023198480799508686654757/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (26292454362908167023198480799508686654757/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (1050653061530504327007844809024270976597/200000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1050653061530504327007844809024270976597/200000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1989 BracketBatch0124.bracket1990 (1050653061530504327007844809024270976597/200000000000000000000000000000000000000) (965200205217778936978725954764055465989/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1989 BracketBatch0124.bracket1990
  (1050653061530504327007844809024270976597/200000000000000000000000000000000000000) (965200205217778936978725954764055465989/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1989
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1990
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0310.rows BesselBatch0310.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (52584908725816334046396961599017373309511/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (52584908725816334046396961599017373309511/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (52689850464172261951034229865651644817221/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (52689850464172261951034229865651644817221/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (26318689797497148999357797866167254531683/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (26318689797497148999357797866167254531683/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1990 BracketBatch0124.bracket1991 (26318689797497148999357797866167254531683/5000000000000000000000000000000000000000) (1932906194181114196058587627494858972949/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1990 BracketBatch0124.bracket1991
  (26318689797497148999357797866167254531683/5000000000000000000000000000000000000000) (1932906194181114196058587627494858972949/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1990
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1991
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (26344925232086130975517114932825822408609/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26344925232086130975517114932825822408609/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (3299701581102548813611428739017048619853/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3299701581102548813611428739017048619853/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (52742537880906521484408544844962211367433/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (52742537880906521484408544844962211367433/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0248.rows ScalarLogs0248.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1991 BracketBatch0124.bracket1992 (52742537880906521484408544844962211367433/10000000000000000000000000000000000000000) (1935417760474576225756743989150619079383/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1991 BracketBatch0124.bracket1992
  (52742537880906521484408544844962211367433/10000000000000000000000000000000000000000) (1935417760474576225756743989150619079383/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1991
