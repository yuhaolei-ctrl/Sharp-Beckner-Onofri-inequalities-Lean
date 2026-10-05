import BecknerOnofri.EntropyScalarCertificate.Bessel0335
import BecknerOnofri.EntropyScalarCertificate.Bessel0336
import BecknerOnofri.EntropyScalarCertificate.Bessel0656
import BecknerOnofri.EntropyScalarCertificate.Bessel0657
import BecknerOnofri.EntropyScalarCertificate.Brackets0134
import BecknerOnofri.EntropyScalarCertificate.Logs0268
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2144
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (38084467653344843187957200403300997774707/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (38084467653344843187957200403300997774707/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (38196742347661199273086082235859086101629/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (38196742347661199273086082235859086101629/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (4767575625062877653815205164947505242271/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4767575625062877653815205164947505242271/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2144 BracketBatch0134.bracket2145 (4767575625062877653815205164947505242271/625000000000000000000000000000000000000) (120351675898672739670443375977092362047/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2144 BracketBatch0134.bracket2145
  (4767575625062877653815205164947505242271/625000000000000000000000000000000000000) (120351675898672739670443375977092362047/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2144
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2145
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (15278696939064479709234432894343634440651/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15278696939064479709234432894343634440651/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (19154847075062260931259337331827460117979/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19154847075062260931259337331827460117979/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (153012872995571442271209513799028012675171/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (153012872995571442271209513799028012675171/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2145 BracketBatch0134.bracket2146 (153012872995571442271209513799028012675171/20000000000000000000000000000000000000000) (602714202879637640819864163989067430327/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2145 BracketBatch0134.bracket2146
  (153012872995571442271209513799028012675171/20000000000000000000000000000000000000000) (602714202879637640819864163989067430327/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2145
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2146
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (76619388300249043725037349327309840471913/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (76619388300249043725037349327309840471913/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (15369331678754050592157448316470012764267/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15369331678754050592157448316470012764267/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (1198953489797025755358004616481718002291/156250000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1198953489797025755358004616481718002291/156250000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2146 BracketBatch0134.bracket2147 (1198953489797025755358004616481718002291/156250000000000000000000000000000000000) (603673176225773411315189904489132188201/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2146 BracketBatch0134.bracket2147
  (1198953489797025755358004616481718002291/156250000000000000000000000000000000000) (603673176225773411315189904489132188201/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2146
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2147
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (19211664598442563240196810395587515955333/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19211664598442563240196810395587515955333/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (15415061479389109784671403987122170029083/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15415061479389109784671403987122170029083/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (153921965790715801884144261517960913966747/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (153921965790715801884144261517960913966747/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2147 BracketBatch0134.bracket2148 (153921965790715801884144261517960913966747/20000000000000000000000000000000000000000) (2418541275966083490140403369691974858743/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2147 BracketBatch0134.bracket2148
  (153921965790715801884144261517960913966747/20000000000000000000000000000000000000000) (2418541275966083490140403369691974858743/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2147
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2148
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (19268826849236387230839254983902712536353/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19268826849236387230839254983902712536353/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (38652673940927050747055282265022860278963/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (38652673940927050747055282265022860278963/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (77190327639399825208733792232828285351669/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (77190327639399825208733792232828285351669/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2148 BracketBatch0134.bracket2149 (77190327639399825208733792232828285351669/10000000000000000000000000000000000000000) (605600650815193241689717400045385424791/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2148 BracketBatch0134.bracket2149
  (77190327639399825208733792232828285351669/10000000000000000000000000000000000000000) (605600650815193241689717400045385424791/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2148
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2149
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (77305347881854101494110564530045720557923/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (77305347881854101494110564530045720557923/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (969209907173710484956342846552952866033/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (969209907173710484956342846552952866033/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (154842140455750940290617992254281949840563/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (154842140455750940290617992254281949840563/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2149 BracketBatch0134.bracket2150 (154842140455750940290617992254281949840563/20000000000000000000000000000000000000000) (606569191515804377771256766059688938183/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2149 BracketBatch0134.bracket2150
  (154842140455750940290617992254281949840563/20000000000000000000000000000000000000000) (606569191515804377771256766059688938183/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2149
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2150
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0335.rows BesselBatch0335.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (77536792573896838796507427724236229282637/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (77536792573896838796507427724236229282637/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (38884827177070399475189174348416003665817/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (38884827177070399475189174348416003665817/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (155306446928037637746885776421068236614271/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (155306446928037637746885776421068236614271/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2150 BracketBatch0134.bracket2151 (155306446928037637746885776421068236614271/20000000000000000000000000000000000000000) (2430163844380950055381639576078316959187/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2150 BracketBatch0134.bracket2151
  (155306446928037637746885776421068236614271/20000000000000000000000000000000000000000) (2430163844380950055381639576078316959187/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2150
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2151
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (77769654354140798950378348696832007331631/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (77769654354140798950378348696832007331631/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0336.rows BesselBatch0336.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (15600789252341325911453723707817233723749/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15600789252341325911453723707817233723749/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0656.rows BesselBatch0656.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0657.rows BesselBatch0657.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (19471700076980928563455870904489771993797/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19471700076980928563455870904489771993797/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0268.rows ScalarLogs0268.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0134.bracket2151 BracketBatch0134.bracket2152 (19471700076980928563455870904489771993797/2500000000000000000000000000000000000000) (2434063918961783923210679964678542832927/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0134.bracket2151 BracketBatch0134.bracket2152
  (19471700076980928563455870904489771993797/2500000000000000000000000000000000000000) (2434063918961783923210679964678542832927/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2151
