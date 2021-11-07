import Init.Data.Array
import Init.Data.Nat

def main : IO Unit :=
  IO.println "Hello, world!"

notation "ℕ" => Nat 

def Array.prod {α} [OfNat α 1] [Mul α] (arr : Array α) := 
  Array.foldl (λ x y => x * y) 1 arr

notation "∏" => Array.prod

instance {n} : OfNat Type n := {ofNat := Fin n}
instance : Mul Type := {mul := Prod}

class AsFunction (α : Type) :=
  (args : α → Array Type)
  (result : α → Type)
  (toFun :∀ α, (∏ (args α)) → result α)

open AsFunction

structure Node (rows cols reachBack : ℕ) (func : Type) [AsFunction func] : Type :=
  (tag : func)
  (args : Fin (args tag).size → (Fin rows × Fin cols))

structure CartGenome (rows cols reachBack : ℕ) (func : Type) [AsFunction func] :=
  (
    nodes : Fin cols → Fin rows → Node rows cols reachBack func
  )

