import Lean

universe u

inductive PDist : Type → Type _
  | randNat : (lo hi : Nat) → PDist Nat
  | pure {α : Type} : α → PDist α
  | bind {α β : Type} : PDist α → (α → PDist β) → PDist β

namespace PDist

instance : Monad PDist where
  pure := pure
  bind := bind

def sample : PDist α → IO α
  | randNat lo hi => IO.rand lo hi
  | pure x => return x
  | bind d f => d.sample >>= fun a => (f a).sample

def uniformFinSucc (n : Nat) : PDist (Fin (n + 1)) :=
  return (Fin.ofNat <| ← randNat 0 n)

def uniformFin (n : Nat) (hn : n ≠ 0 := by decide) : PDist (Fin n) :=
  match n with
    | n+1 => uniformFinSucc n
    | 0 => False.elim <| hn rfl

def uniformList (L : List α) (hL : L ≠ [] := by decide) : PDist α := do
  match h : L.length with
    | n+1 =>
        let i ← uniformFin (n + 1) Nat.noConfusion
        return L[i]' (by simp [h, i.isLt])
    | 0 => False.elim <| hL <| by { induction L ; rfl ; simp at h }

def uniformList? (L : List α) : PDist (Option α) :=
  match L with
    | [] => return none
    | (a :: as) => uniformList (a :: as) List.noConfusion <&> some

def uniformList! (L : List α) [Inhabited α] : PDist α := do
  match ← uniformList? L with
    | none => return default
    | some x => return x

def bernoulli : PDist Bool := return (← randNat 0 1) == 0

def stdUniform (res := 2147483562) : PDist Float :=
  return (← randNat 0 (res - 1)).toFloat / (res - 1).toFloat

def uniform (a b : Float) (res := 2147483562) : PDist Float :=
  return a + (b - a) * (← stdUniform res)

def PI : Float :=
  3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211

def stdNormal (res := 2147483562) : PDist Float := do
  let u₁ ← stdUniform res
  let u₂ ← stdUniform res
  return Float.sqrt (-2 * Float.log u₁) * Float.cos (2 * PI * u₂)

def normal (μ σ : Float) (res := 2147483562) : PDist Float :=
  return μ + σ * (← stdNormal res)

def randomList (d : PDist α) (length : Nat) :
    PDist (List α) :=
  match length with
    | 0 => return []
    | n+1 => return (← d) :: (← randomList d n)
