
import Mathlib.CategoryTheory.Category.Preorder
import GroupoidModel.FibrationForMathlib.Displayed.Fiber

import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.PenroseDiagram
import Mathlib.Tactic.Widget.CommDiag
import ProofWidgets.Component.Panel.SelectionPanel
import ProofWidgets.Component.Panel.GoalTypePanel


/-! ## Example use of commutative diagram widgets -/

universe u
namespace CategoryTheory
open ProofWidgets

/-- Local instance to make examples work. -/
local instance : Category (Type u) where
  Hom α β := α → β
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

example {f g : Nat ⟶ Bool} : f = g → (f ≫ 𝟙 Bool) = (g ≫ 𝟙 Bool) := by
  with_panel_widgets [GoalTypePanel]
    intro h
    exact h

example {fButActuallyTheNameIsReallyLong g : Nat ⟶ Bool} : fButActuallyTheNameIsReallyLong = g →
    fButActuallyTheNameIsReallyLong = (g ≫ 𝟙 Bool) := by
  with_panel_widgets [GoalTypePanel]
    intro h
    conv =>
      rhs
      enter [1]
      rw [← h]
    rfl

-- from Sina Hazratpour
example {X Y Z : Type} {f g : X ⟶ Y} {k : Y ⟶ Y} {f' : Y ⟶ Z} {i : X ⟶ Z}
    (h': g ≫ f' = i) :
    (f ≫ k) = g → ((f ≫ k) ≫ f') = (g ≫ 𝟙 Y ≫ f') := by
  with_panel_widgets [GoalTypePanel, SelectionPanel]
    intro h
    rw [
      h,
      ← Category.assoc g (𝟙 Y) f',
      h',
      Category.comp_id g,
      h'
    ]

example {X Y Z : Type} {f i : X ⟶ Y}
    {g j : Y ⟶ Z} {h : X ⟶ Z} :
    h = f ≫ g →
    i ≫ j = h →
    f ≫ g = i ≫ j := by
  with_panel_widgets [SelectionPanel]
    intro h₁ h₂
    rw [← h₁, h₂]

/-! Extraction -> Layout -> Rendering -/

/-! ## 2. Layout + Rendering -/

-- open Jsx in
-- #html <PenroseDiagram
--     dsl="type Blob"

--     sty="forall Blob b {
--       b.circ = Circle {}
--       b.text = Equation { string: b.label }
--       ensure contains(b.circ, b.text)
--     }"

--     sub="Blob b
--     Label b \"\\beta\\lambda\\omega\\beta\""
--   />

-- open Jsx in
-- #html <PenroseDiagram
--     dsl={include_str ".."/"widget"/"src"/"penrose"/"commutative.dsl"}
--     sty={include_str ".."/"widget"/"src"/"penrose"/"commutative.sty"}

--     sub="
--     Object W, P, X, Y, Z
--     Cell f := MakeCell(X, Z)
--     Cell g := MakeCell(Y, Z)
--     Cell p1 := MakeCell(P, X)
--     Cell p2 := MakeCell(P, Y)
--     Cell i := MakeCell(W, X)
--     Cell j := MakeCell(W, Y)
--     Cell ij := MakeCell(W, P)

--     IsRightHorizontal(f)
--     IsDownVertical(g)
--     IsDownVertical(p1)
--     IsRightHorizontal(p2)
--     IsRightDownDiagonal(ij)
--     IsCurvedRight(i)
--     IsCurvedLeft(j)

--     IsLabelRight(f)
--     IsLabelLeft(g)
--     IsLabelRight(p1)
--     IsLabelLeft(p2)
--     IsLabelRight(i)
--     IsLabelLeft(j)

--     IsDashed(ij)

--     Label p1 \"\\pi_1\"
--     Label p2 \"\\pi_2\"
--     "
--   />

-- /-! ## 1. Extraction -/

-- open Lean Meta
-- open Mathlib.Tactic.Widget

-- open Jsx in
-- /-- Given a `e : PullbackCone f g`,
-- produce an informative diagram. Otherwise `none`. -/
-- def pullbackConeM? (e : Expr) : MetaM (Option Html) := do
--   let eTp ← inferType e
--   let eTp ← instantiateMVars eTp
--   let some (_, _, _, _, _, f, g) := eTp.app7? ``Limits.PullbackCone | return none
--   let fst ← mkAppM ``Limits.PullbackCone.fst #[e]
--   let snd ← mkAppM ``Limits.PullbackCone.snd #[e]
--   let some (X, Z) := homType? (← inferType f >>= instantiateMVars) | return none
--   let some (W, Y) := homType? (← inferType snd >>= instantiateMVars) | return none

--   some <$> mkCommDiag
--     "
--     Object W, X, Y, Z
--     Cell f := MakeCell(X, Z)
--     Cell g := MakeCell(Y, Z)
--     IsRightHorizontal(f)
--     IsDownVertical(g)

--     Cell i := MakeCell(W, X)
--     Cell j := MakeCell(W, Y)
--     IsDownVertical(i)
--     IsRightHorizontal(j)
--     "
--     #[("f", f), ("g", g), ("i", fst), ("j", snd),
--       ("W", W), ("X", X), ("Y", Y), ("Z", Z)]

-- @[expr_presenter]
-- def pullbackPresenter : ExprPresenter where
--   userName := "Pullback cone"
--   layoutKind := .block
--   present type := do
--     if let some d ← pullbackConeM? type then
--       return d
--     throwError "Couldn't find a pullback."

-- example {f : Nat ⟶ Nat} :
--     ∃ (P : Type) (fst snd : P ⟶ Nat),
--     IsPullback fst snd f f := by

--   with_panel_widgets [SelectionPanel]

--     let P := { nm : Nat × Nat // f nm.1 = f nm.2 }
--     let fst : P ⟶ Nat := fun p => p.val.1
--     let snd : P ⟶ Nat := fun p => p.val.2

--     have : IsPullback fst snd f f := {
--       isLimit' := ⟨{
--         lift := fun c w => by
--           let c : Limits.PullbackCone _ _ := c
--           exact ⟨(c.fst w, c.snd w), congrFun c.condition w⟩

--         fac := by
--           intro c j
--           let c : Limits.PullbackCone _ _ := c
--           ext w
--           rcases j with _ | ⟨_ | _⟩ <;> simp

--         uniq := by
--           intro s f h; ext w
--           dsimp
--           ext
--           . simpa using congrFun (h .left) w
--           . simpa using congrFun (h .right) w
--       }⟩
--       w := funext (·.property)
--     }

--     exact ⟨P, fst, snd, by assumption⟩

-- /- Ideas:
-- structure State where
--   objs : Array Expr
--   homs : Array (Nat × Nat × Expr)
--   commutingPaths : Array (Array Nat × Array Nat)

-- @[expr_extractor]
-- def (e : Expr) -> StateM State Unit




-- -/
