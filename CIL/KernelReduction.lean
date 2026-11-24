import Lean

/-!
# Kernel reduction from elaborator code

Commands that must decide a term the elaborator's `whnf` leaves stuck, such as a definition by
well-founded recursion or one marked irreducible, ask the kernel through `kernelWhnf`.
-/

namespace CIL

open Lean Meta

/-- The weak head normal form of `term` in the current local context as the kernel reduces it,
    unfolding every definition whatever its reducibility; a kernel failure is thrown. -/
def kernelWhnf (term : Expr) : MetaM Expr := do
  ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) term)

end CIL
