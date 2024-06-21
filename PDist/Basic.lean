import Lean

universe u

abbrev PDistT := StateT StdGen

namespace PDistT

variable {M : Type → Type} [Monad M]

def randNat (lo hi : Nat) : PDistT M Nat := do
  let ⟨out, next⟩ := _root_.randNat (← get) lo hi
  set next
  return out

def randFin (n : Nat) : PDistT M (Fin <| n+1) := do
  let ⟨out, next⟩ := _root_.randNat (← get) 0 n
  set next
  return Fin.ofNat out

def randBool : PDistT M Bool := do
  let (out, next) := _root_.randBool (← get)
  set next
  return out

def sampleWith (seed : Nat) (e : PDistT M α) : M α := do
  e.run' (mkStdGen seed)

def sample [MonadLiftT (ST IO.RealWorld) M] (e : PDistT M α) :
    M α := do
  let stdgen ← IO.stdGenRef.get
  let (out, next) ← e.run stdgen
  IO.stdGenRef.set next
  return out

end PDistT

abbrev PDist := PDistT Id

namespace PDist

def sample [Monad M] (a : PDist α) [MonadLiftT (ST IO.RealWorld) M] : M α := do
  let stdgen ← IO.stdGenRef.get
  let (out, next) := a.run stdgen
  IO.stdGenRef.set next
  return out

def sampleWith (seed : Nat) (a : PDist α) : α :=
  PDistT.sampleWith seed a

end PDist
