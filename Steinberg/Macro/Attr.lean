/-

Declares class and simp attributes for the Steinberg project.

These attributes are used to tag certain theorem for use in
custom tactics (see `Macro/Group`).

-/

import Mathlib.Tactic.Attr.Register

namespace Steinberg

register_simp_attr chev_simps

end Steinberg
