import Mathlib.CategoryTheory.Comma.Over


import Lean
open Lean

def foo (A : Type u) : Type u := A × A -- just as an example.

def foo.forget {A : Type u} : foo A → A := Prod.fst
def foo.map {A : Type u} : foo A → foo A := fun (a,b) => (b,a)

open Lean Elab Meta
elab "Σ_ " t:term : term => do
  let t ← Term.elabTerm t none
  let tp ← Meta.inferType t
  match tp with
  | .app (.const ``foo [u]) A => return .app (.const ``foo.map [u]) A
  | _ =>
    let .sort (.succ u) ← Meta.inferType tp | throwError "ERROR"
    return .app (.const ``foo.forget [u]) tp


variable (x : foo Nat) (y : Nat)

#check Σ_ x
#check Σ_ y


open CategoryTheory Category Over

#check Over.forget
#check Over.map


inductive ObjOrMor (C : Type*) [Category C] where
  | obj : C → ObjOrMor C
  | mor {X Y : C} : (X ⟶ Y) → ObjOrMor C


section

variable (C : Type*) [Category C]

def Homm (C : Type*) [Category C] (X Y : C) := Quiver.Hom X Y

def dom {X Y : C} (f : X ⟶ Y) : C := X

def cod {X Y : C} (f : X ⟶ Y) : C := Y

open Lean Elab Meta
-- elab "Σ_ " t:term : term => do
--   let t ← Term.elabTerm t none
--   let tp ← Meta.inferType t
--   match tp with
--   | .app (.const `Quiver.Hom` [u]) (dom t) (cod t) => return .app (.const ``Over.forget [u]) A
--   | _ =>
--     let .sort (.succ u) ← Meta.inferType tp | throwError "ERROR"
--     return .app (.const ``Over.forget [u]) tp

end


section
variable {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y)


end



def forgetOrMap {C : Type*} [Category C] : ObjOrMor C → (Π (X: C), Over X ⥤ C) ⊕ (Π {X Y : C} (_ : X ⟶ Y), Over X ⥤ Over Y) := fun
  | .obj _ => .inl (Over.forget)
  | .mor _ => .inr (Over.map)




-- set_option quotPrecheck false
-- scoped notation "Σ_" => fun (x : ObjOrMor C) => match x with
--   | .obj I => (Over.forget I)
--   | .mor f => (Over.map f)
