import BecknerOnofri.EntropyScalarCertificate.Bessel0180
import BecknerOnofri.EntropyScalarCertificate.Bessel0181
import BecknerOnofri.EntropyScalarCertificate.Bessel0578
import BecknerOnofri.EntropyScalarCertificate.Bessel0579
import BecknerOnofri.EntropyScalarCertificate.Brackets0072
import BecknerOnofri.EntropyScalarCertificate.Logs0144
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1152
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (2079203234361663396898901818243242760587/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2079203234361663396898901818243242760587/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (1042488697291858213170995072465372451541/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1042488697291858213170995072465372451541/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (4164180628945379823240891963173987663669/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4164180628945379823240891963173987663669/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1152 BracketBatch0072.bracket1153 (4164180628945379823240891963173987663669/5000000000000000000000000000000000000000) (154422039333073795967192376306809618819/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1152 BracketBatch0072.bracket1153
  (4164180628945379823240891963173987663669/5000000000000000000000000000000000000000) (154422039333073795967192376306809618819/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1152
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1153
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (333596383133394628214718423188919184493/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (333596383133394628214718423188919184493/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (8363093310852312953561086721820574105079/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8363093310852312953561086721820574105079/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (4175750722296794664732261825385888429351/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4175750722296794664732261825385888429351/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1153 BracketBatch0072.bracket1154 (4175750722296794664732261825385888429351/5000000000000000000000000000000000000000) (155533429244920811834054037925217126603/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1153 BracketBatch0072.bracket1154
  (4175750722296794664732261825385888429351/5000000000000000000000000000000000000000) (155533429244920811834054037925217126603/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1153
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1154
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (2090773327713078238390271680455143526269/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2090773327713078238390271680455143526269/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (2096591213627445136604279083202873756557/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2096591213627445136604279083202873756557/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (2093682270670261687497275381829008641413/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2093682270670261687497275381829008641413/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1154 BracketBatch0072.bracket1155 (2093682270670261687497275381829008641413/2500000000000000000000000000000000000000) (31330364846937961508454838127783323909/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1154 BracketBatch0072.bracket1155
  (2093682270670261687497275381829008641413/2500000000000000000000000000000000000000) (31330364846937961508454838127783323909/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1154
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1155
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (335454594180391221856684653312459801049/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (335454594180391221856684653312459801049/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (8409724937009911219606306512336034286517/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8409724937009911219606306512336034286517/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (8398044895759845883011711422573764656371/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8398044895759845883011711422573764656371/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1155 BracketBatch0072.bracket1156 (8398044895759845883011711422573764656371/10000000000000000000000000000000000000000) (78888634524275948503645094694075654233/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1155 BracketBatch0072.bracket1156
  (8398044895759845883011711422573764656371/10000000000000000000000000000000000000000) (78888634524275948503645094694075654233/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1155
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1156
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (4204862468504955609803153256168017143257/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4204862468504955609803153256168017143257/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (8433174294367267805104608083834782579961/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8433174294367267805104608083834782579961/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (673715969255087160988436583846832674659/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (673715969255087160988436583846832674659/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1156 BracketBatch0072.bracket1157 (673715969255087160988436583846832674659/800000000000000000000000000000000000000) (158909808819964486414057836573373222869/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1156 BracketBatch0072.bracket1157
  (673715969255087160988436583846832674659/800000000000000000000000000000000000000) (158909808819964486414057836573373222869/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1156
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1157
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (4216587147183633902552304041917391289979/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4216587147183633902552304041917391289979/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (8456713671030521540040859303762786816219/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8456713671030521540040859303762786816219/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (16889887965397789345145467387597569396177/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16889887965397789345145467387597569396177/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1157 BracketBatch0072.bracket1158 (16889887965397789345145467387597569396177/20000000000000000000000000000000000000000) (8002474453734358749928329450744990141/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1157 BracketBatch0072.bracket1158
  (16889887965397789345145467387597569396177/20000000000000000000000000000000000000000) (8002474453734358749928329450744990141/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1157
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1158
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (1057089208878815192505107412970348352027/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1057089208878815192505107412970348352027/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (4240171910003404994893925404315627844917/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4240171910003404994893925404315627844917/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (338741149820746630596574202247880850121/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (338741149820746630596574202247880850121/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1158 BracketBatch0072.bracket1159 (338741149820746630596574202247880850121/400000000000000000000000000000000000000) (16119635573588055379305365245128300817/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1158 BracketBatch0072.bracket1159
  (338741149820746630596574202247880850121/400000000000000000000000000000000000000) (16119635573588055379305365245128300817/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1158
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1159
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (8480343820006809989787850808631255689831/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8480343820006809989787850808631255689831/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0181.rows BesselBatch0181.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (2126016375747077373650355340455816185247/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2126016375747077373650355340455816185247/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0579.rows BesselBatch0579.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (16984409322995119484389272170454520430819/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16984409322995119484389272170454520430819/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0144.rows ScalarLogs0144.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0072.bracket1159 BracketBatch0072.bracket1160 (16984409322995119484389272170454520430819/20000000000000000000000000000000000000000) (162350455129289478937290923455231399301/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0072.bracket1159 BracketBatch0072.bracket1160
  (16984409322995119484389272170454520430819/20000000000000000000000000000000000000000) (162350455129289478937290923455231399301/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1159
