/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import ConflictClauseLattice.PosetLattice

namespace ConflictClauseLattice

/-! ### Section III: Simplicial Order Complex, Boundary Operators `∂_{k-1} ∘ ∂_k = 0`, and Model Counting -/

/-- A 1-simplex in the order complex of `L_Φ` is an ordered pair `(v0, v1)`. -/
structure Simplex1 where
  v0 : ValidClause3
  v1 : ValidClause3
  deriving DecidableEq, Repr

/-- A 2-simplex in the order complex of `L_Φ` is a chain of 3 clauses `(v0, v1, v2)`. -/
structure Simplex2 where
  v0 : ValidClause3
  v1 : ValidClause3
  v2 : ValidClause3
  deriving DecidableEq, Repr

/-- Evaluation of the 1-boundary `∂₁` of a 1-simplex `(v0, v1)` against any 0-cochain `f : ValidClause3 → Int`:
    `⟨f, ∂₁(v0, v1)⟩ = f(v1) - f(v0)`. -/
def evalBoundary1 (f : ValidClause3 → Int) (e : Simplex1) : Int :=
  f e.v1 - f e.v0

/-- Evaluation of the iterated boundary `∂₁(∂₂(v0, v1, v2))` of a 2-simplex
    `∂₂(v0, v1, v2) = (v1, v2) - (v0, v2) + (v0, v1)` against any 0-cochain `f`:
    `⟨f, ∂₁(∂₂(v0, v1, v2))⟩ = ∂₁(v1, v2) - ∂₁(v0, v2) + ∂₁(v0, v1)`. -/
def evalBoundary1OfBoundary2 (f : ValidClause3 → Int) (s : Simplex2) : Int :=
  evalBoundary1 f ⟨s.v1, s.v2⟩ - evalBoundary1 f ⟨s.v0, s.v2⟩ + evalBoundary1 f ⟨s.v0, s.v1⟩

/-- Fundamental Homological Identity `∂₁ ∘ ∂₂ = 0` on every 2-simplex of the Conflict-Clause Poset Lattice. -/
theorem boundary1_comp_boundary2_eq_zero (f : ValidClause3 → Int) (s : Simplex2) :
    evalBoundary1OfBoundary2 f s = 0 := by
  dsimp [evalBoundary1OfBoundary2, evalBoundary1]
  omega

/-- Higher-order simplicial boundary identity `∂₂ ∘ ∂₃ = 0` on every 3-simplex `(v0, v1, v2, v3)`
    spanning all 4 layers (L₀ → L₁ → L₂ → L₃) of the Conflict-Clause Poset Lattice,
    tested against any 1-cochain `g : Simplex1 → Int` via `∂₂`. -/
def evalBoundary2 (g : Simplex1 → Int) (s : Simplex2) : Int :=
  g ⟨s.v1, s.v2⟩ - g ⟨s.v0, s.v2⟩ + g ⟨s.v0, s.v1⟩

def evalBoundary2OfBoundary3 (g : Simplex1 → Int) (v0 v1 v2 v3 : ValidClause3) : Int :=
  evalBoundary2 g ⟨v1, v2, v3⟩ - evalBoundary2 g ⟨v0, v2, v3⟩ +
  evalBoundary2 g ⟨v0, v1, v3⟩ - evalBoundary2 g ⟨v0, v1, v2⟩

theorem boundary2_comp_boundary3_eq_zero (g : Simplex1 → Int) (v0 v1 v2 v3 : ValidClause3) :
    evalBoundary2OfBoundary3 g v0 v1 v2 v3 = 0 := by
  dsimp [evalBoundary2OfBoundary3, evalBoundary2]
  omega

/-- Euler-Poincaré alternating rank sum across all 4 graded layers of `L₃`:
    `|L₀| - |L₁| + |L₂| - |L₃| = 1 - 6 + 12 - 8 = -1`. -/
theorem euler_poincare_L3 :
    ((clausesOfRank3 0).length : Int) - ((clausesOfRank3 1).length : Int) +
    ((clausesOfRank3 2).length : Int) - ((clausesOfRank3 3).length : Int) = -1 := by
  decide

/-- Non-empty conflict sublattice alternating rank sum:
    `|L₁| - |L₂| + |L₃| = 6 - 12 + 8 = 2`. -/
theorem non_empty_euler_characteristic_L3 :
    ((clausesOfRank3 1).length : Int) - ((clausesOfRank3 2).length : Int) +
    ((clausesOfRank3 3).length : Int) = 2 := by
  decide

/-! ### Exact Bijection Between Satisfying Assignments `#3-SAT(Φ)` and Unobstructed Lattice Atoms -/

/-- A truth assignment `α : {x₁, x₂, x₃} → Bool`. -/
structure Assignment3 where
  a1 : Bool
  a2 : Bool
  a3 : Bool
  deriving DecidableEq, Repr

/-- All 2³ = 8 truth assignments on `{x₁, x₂, x₃}`. -/
def allAssignments3 : List Assignment3 :=
  [false, true].flatMap (fun b1 =>
    [false, true].flatMap (fun b2 =>
      [false, true].map (fun b3 => ⟨b1, b2, b3⟩)))

/-- Whether a single variable polarity state in a clause is satisfied by assignment bit `b`. -/
def varStateSat (s : VarState) (b : Bool) : Bool :=
  match s with
  | none => false
  | some p => p == b

/-- Whether a clause `c ∈ L₃` is satisfied by assignment `α`.
    Note that the empty clause `∅` is unsatisfiable (`false`). -/
def satisfiesClause (α : Assignment3) (c : ValidClause3) : Bool :=
  varStateSat c.x1 α.a1 || varStateSat c.x2 α.a2 || varStateSat c.x3 α.a3

/-- Whether a CNF formula `Φ : List ValidClause3` is satisfied by assignment `α`. -/
def satisfiesFormula (α : Assignment3) (Φ : List ValidClause3) : Bool :=
  Φ.all (fun c => satisfiesClause α c)

/-- Exact model count `#3-SAT(Φ)` by counting satisfying truth assignments. -/
def modelCount3 (Φ : List ValidClause3) : Nat :=
  (allAssignments3.filter (fun α => satisfiesFormula α Φ)).length

/-- The canonical dual Layer-3 full-clause atom `A_α` obstructed by assignment `α`:
    `A_α` has negated polarity `¬α(xᵢ)` on each variable, so `α` is the unique assignment
    that falsifies `A_α`. -/
def dualAtomOfAssignment (α : Assignment3) : ValidClause3 :=
  ⟨some (!α.a1), some (!α.a2), some (!α.a3)⟩

/-- An atom `A ∈ Layer₃(L₃)` is unobstructed by formula `Φ` iff no clause `c ∈ Φ` implies `A`
    (`∀ c ∈ Φ, ¬(c ≼ A)`). -/
def isUnobstructedAtom (Φ : List ValidClause3) (atom : ValidClause3) : Bool :=
  Φ.all (fun c => !isImplied c atom)

/-- Count of unobstructed Layer-3 atoms in the Conflict-Clause Poset Lattice `L₃`. -/
def unobstructedAtomCount3 (Φ : List ValidClause3) : Nat :=
  ((clausesOfRank3 3).filter (fun atom => isUnobstructedAtom Φ atom)).length

/-- Single-variable duality: `varStateSat s b = !varStateSub s (some (!b))`. -/
theorem varStateSat_eq_not_varStateSub (s : VarState) (b : Bool) :
    varStateSat s b = !varStateSub s (some (!b)) := by
  rcases s with _ | (_ | _) <;> cases b <;> rfl

/-- Key Duality Lemma: An assignment `α` satisfies a clause `c ∈ L₃` if and only if
    `c` does NOT imply the dual Layer-3 atom `dualAtomOfAssignment α`. -/
theorem satisfiesClause_iff_not_implies_dualAtom (α : Assignment3) (c : ValidClause3) :
    satisfiesClause α c = !isImplied c (dualAtomOfAssignment α) := by
  unfold satisfiesClause isImplied dualAtomOfAssignment
  rw [varStateSat_eq_not_varStateSub c.x1 α.a1,
      varStateSat_eq_not_varStateSub c.x2 α.a2,
      varStateSat_eq_not_varStateSub c.x3 α.a3]
  cases varStateSub c.x1 (some (!α.a1)) <;>
  cases varStateSub c.x2 (some (!α.a2)) <;>
  cases varStateSub c.x3 (some (!α.a3)) <;> rfl

/-- Formula Duality Theorem: An assignment `α` satisfies formula `Φ` if and only if
    its dual Layer-3 atom `dualAtomOfAssignment α` is unobstructed in the poset `L₃`. -/
theorem satisfiesFormula_eq_isUnobstructed_dualAtom (α : Assignment3) (Φ : List ValidClause3) :
    satisfiesFormula α Φ = isUnobstructedAtom Φ (dualAtomOfAssignment α) := by
  induction Φ with
  | nil => rfl
  | cons c cs ih =>
    unfold satisfiesFormula isUnobstructedAtom at *
    rw [List.all_cons, List.all_cons, satisfiesClause_iff_not_implies_dualAtom, ih]

/-- Bijection between `allAssignments3` under `dualAtomOfAssignment` and `clausesOfRank3 3`. -/
theorem dualAtoms_eq_layer3 :
    allAssignments3.map dualAtomOfAssignment = clausesOfRank3 3 := by
  decide

/-- Theorem 1 (Finite Kernel-Verified Realization):
    For any CNF formula `Φ` over `{x₁, x₂, x₃}`, the exact model count `#3-SAT(Φ)`
    equals the number of unobstructed Layer-3 atoms in the Conflict-Clause Poset Lattice `L₃`. -/
theorem modelCount3_eq_unobstructedAtomCount3 (Φ : List ValidClause3) :
    modelCount3 Φ = unobstructedAtomCount3 Φ := by
  unfold modelCount3 unobstructedAtomCount3
  rw [← dualAtoms_eq_layer3]
  rw [List.filter_map]
  rw [List.length_map]
  congr 1
  apply List.filter_congr
  intro α _
  simp only [Function.comp, satisfiesFormula_eq_isUnobstructed_dualAtom]

end ConflictClauseLattice
