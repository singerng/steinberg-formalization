/-

LICENSE goes here.

-/

import Steinberg.Macro.Group

namespace Steinberg

class PosRootSys (Root : semiOutParam (Type TΦ))
  extends
    ToString Root
  where
  height : Root → Nat

attribute [height_simps] PosRootSys.height

end Steinberg
