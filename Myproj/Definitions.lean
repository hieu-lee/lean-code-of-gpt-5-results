-- Central wrapper module: re-export Definitions submodules to keep imports stable.

import Myproj.Definitions.Cyclics
import Myproj.Definitions.RpowIneq
import Myproj.Definitions.IteratedLogs
import Myproj.Definitions.RealCounting
import Myproj.Definitions.Primes
import Myproj.Definitions.NearSquares
import Myproj.Definitions.LegendreCyclics

noncomputable section

namespace Myproj

open Filter

/-- Counting function of cyclic numbers up to `N` (cast to `ℝ`). -/
def cyclicCountUpTo (N : ℕ) : ℝ :=
  ((Finset.Icc 1 N).filter (fun n => isCyclicNumber n)).card

end Myproj

end
