#!/usr/bin/env python3
"""Generate SolutionRoute.lean from Solution.lean: same 28 statements, proofs replaced by the
route-aligned declarations of BecknerOnofri.V2.Reaudit (second pass).  Statements are copied verbatim."""
import re, sys
src = open('Solution.lean').read()
M = 'BecknerOnofri.V2.Reaudit.Mixtures.'
F = 'BecknerOnofri.V2.Reaudit.Final.'
S = 'BecknerOnofri.V2.Reaudit.SpinChannel.'
bodies = {
 'low_dim_entropy_inequality': M+'low_dim_entropy_inequality d hd hd10 ρ',
 'low_dim_beckner_onofri': M+'low_dim_beckner_onofri d hd hd10 u hu',
 'low_dim_coefficient_sharp': M+'low_dim_coefficient_sharp d hd hd10',
 'circle_beckner_onofri_eq_iff': M+'circle_beckner_onofri_eq_iff u hu',
 'circle_entropy_eq_iff': M+'circle_entropy_eq_iff ρ hρ',
 'low_dim_entropy_eq_iff': M+'low_dim_entropy_eq_iff d hd hd10 ρ hρ',
 'low_dim_beckner_onofri_eq_iff': M+'low_dim_beckner_onofri_eq_iff d hd hd10 u hu',
 'low_dim_pressure_eq': M+'low_dim_pressure_eq d hd hd10 β',
 'low_dim_defect_eq': M+'low_dim_defect_eq d hd hd10 A',
 'low_dim_globalTransition': M+'low_dim_globalTransition d hd hd10',
 'eleven_profile_constant': 'BecknerOnofri.V2.Final.eleven_profile_constant',
 'eleven_competitor': F+'eleven_competitor_route',
 'eleven_spectral_pressure': F+'eleven_spectral_pressure_route',
 'eleven_globalTransition_bounds': F+'eleven_globalTransition_bounds_route',
 'eleven_coexistence': F+'eleven_coexistence_route',
 'eleven_uniform_hessian_pos': F+'eleven_uniform_hessian_pos_route',
 'eleven_pressure_corner': F+'eleven_pressure_corner_route',
 'eleven_pressure_derivative_jump': F+'eleven_pressure_derivative_jump_route',
 'eleven_defect_corner': F+'eleven_defect_corner_route',
 'high_dim_entropy_inequality': S+'high_dim_entropy_inequality_written d hd ρ',
 'high_dim_entropy_eq_iff': S+'high_dim_entropy_eq_iff_written d hd ρ hρ',
 'high_dim_beckner_onofri': S+'high_dim_beckner_onofri_written d hd u hu',
 'high_dim_beckner_onofri_eq_iff': S+'high_dim_beckner_onofri_eq_iff_written d hd u hu',
 'high_dim_thresholds': S+'high_dim_thresholds_written d hd',
 'kappa_pos': 'BecknerOnofri.V2.Final.kappa_pos d hd',
 'high_dim_onset_branch': F+'Onset.high_dim_onset_branch_route d hd',
 'high_dim_pressure_onset': F+'Onset.high_dim_pressure_onset_route d hd',
 'high_dim_defect_onset': F+'Onset.high_dim_defect_onset_route d hd',
}
out = src
# header
out = out.replace('public import BecknerOnofri.Targets',
  'public import BecknerOnofri.V2.Reaudit.Final.All')
out = out.replace('The statements of `Challenge.lean`, proved from the development. Each theorem is a direct\nconsequence of a result of the library: `BecknerOnofri.Targets` collects the formal\ncounterparts of the paper\'s lemmas, propositions and theorems (see `CORRESPONDENCE.md`).',
  'The statements of `Challenge.lean`, proved from the route-aligned development of the second pass\n(`BecknerOnofri.V2.Reaudit`): each theorem is a direct consequence of a declaration whose proof follows the\nwritten route (low dimensions: `Reaudit.Mixtures`; dimension eleven: `Reaudit.Final.Section4`; `d ≥ 12`:\n`Reaudit.SpinChannel.WrittenEndpoint`).')
for name, body in bodies.items():
    m = re.search(r'theorem '+re.escape(name)+r'\b', out)
    assert m, name
    i = out.index(':=', m.end())
    # end of this declaration: next blank-line-separated docstring or end of file
    nxt = re.search(r'\n\n(?:/--|/-!|end )', out[i:])
    j = i + nxt.start() if nxt else len(out)
    out = out[:i] + ':=\n  ' + body + out[j:]
open('SolutionRoute.lean','w').write(out)
print('ok', len(bodies))
