/-

LICENSE goes here.

-/

namespace Steinberg

class PosRootSys (Root : semiOutParam (Type TΦ))
  extends
    ToString Root
  where
  height : Root → Nat

namespace PosRootSys

instance instCoeNat (R : Type TΦ) [PosRootSys R] : Coe R Nat where
  coe r := PosRootSys.height r

end PosRootSys

end Steinberg
