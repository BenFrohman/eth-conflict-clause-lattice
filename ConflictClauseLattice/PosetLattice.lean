/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

namespace ConflictClauseLattice

/-- Polarity state of a single Boolean variable xᵢ inside a valid (non-contradictory) clause:
    - `none`      : xᵢ does not appear in the clause
    - `some true` : positive literal  xᵢ appears
    - `some false`: negative literal ¬xᵢ appears
    By construction, a variable cannot appear both positively and negatively,
    giving 3 choices per variable and 3ⁿ valid clauses on n variables. -/
abbrev VarState := Option Bool

/-- A valid 3-variable conflict clause over V = {x₁, x₂, x₃}. -/
structure ValidClause3 where
  x1 : VarState
  x2 : VarState
  x3 : VarState
  deriving DecidableEq, Repr, Inhabited

/-- Number of literals (rank / layer index in {0, 1, 2, 3}) of a valid 3-variable clause. -/
def ValidClause3.rank (c : ValidClause3) : Nat :=
  (match c.x1 with | none => 0 | some _ => 1) +
  (match c.x2 with | none => 0 | some _ => 1) +
  (match c.x3 with | none => 0 | some _ => 1)

/-- Empty clause ∅ (Layer 0 top/apex in the Hasse diagram). -/
def emptyClause3 : ValidClause3 := ⟨none, none, none⟩

/-- Componentwise inclusion on a single variable state:
    `s1` is included in `s2` iff `s1 = none` or `s1 = s2`. -/
def varStateSub (s1 s2 : VarState) : Bool :=
  match s1 with
  | none => true
  | some b1 =>
    match s2 with
    | none => false
    | some b2 => b1 == b2

/-- Boolean implication order on valid 3-variable clauses (Definition 1):
    `isImplied c1 c2` holds iff `c1 ⊆ c2` as sets of literals (so `c1 ⊨ c2`). -/
def isImplied (c1 c2 : ValidClause3) : Bool :=
  varStateSub c1.x1 c2.x1 && varStateSub c1.x2 c2.x2 && varStateSub c1.x3 c2.x3

/-- Propositional partial order `c1 ≼ c2` (c1 is a sub-clause of c2, hence logically implies c2). -/
def ImpliesPoset (c1 c2 : ValidClause3) : Prop :=
  isImplied c1 c2 = true

instance (c1 c2 : ValidClause3) : Decidable (ImpliesPoset c1 c2) :=
  inferInstanceAs (Decidable (isImplied c1 c2 = true))

/-- All 3 states for a single variable. -/
def allVarStates : List VarState := [none, some true, some false]

/-- Complete enumeration of all 3³ = 27 valid conflict clauses over {x₁, x₂, x₃},
    matching `getAllClauses(['x1', 'x2', 'x3'])` in `conflict_clause_lattice.html`. -/
def allValidClauses3 : List ValidClause3 :=
  allVarStates.flatMap (fun s1 =>
    allVarStates.flatMap (fun s2 =>
      allVarStates.map (fun s3 => ⟨s1, s2, s3⟩)))

/-- Clauses in Layer `k` (clauses of exact literal size `k`, for k ∈ {0, 1, 2, 3}). -/
def clausesOfRank3 (k : Nat) : List ValidClause3 :=
  allValidClauses3.filter (fun c => c.rank == k)

/-- Immediate covering relation in the Hasse diagram:
    `c1` is covered by `c2` iff `c1 ⊂ c2` and `rank(c2) = rank(c1) + 1`. -/
def covers3 (c1 c2 : ValidClause3) : Bool :=
  isImplied c1 c2 && (c2.rank == c1.rank + 1)

/-- All directed covering edges (c1, c2) in the 3-variable Conflict-Clause Poset Lattice. -/
def coveringEdges3 : List (ValidClause3 × ValidClause3) :=
  allValidClauses3.flatMap (fun c1 =>
    (allValidClauses3.filter (fun c2 => covers3 c1 c2)).map (fun c2 => (c1, c2)))

/-- Covering edges originating from Layer `k` (connecting Layer `k` to Layer `k + 1`). -/
def coveringEdgesFromRank3 (k : Nat) : List (ValidClause3 × ValidClause3) :=
  coveringEdges3.filter (fun p => p.1.rank == k)

/-- Meet operation (∧) on valid clauses: literal intersection `C₁ ∩ C₂`.
    Always produces a valid non-contradictory clause. -/
def varStateMeet (s1 s2 : VarState) : VarState :=
  match s1, s2 with
  | some b1, some b2 => if b1 == b2 then some b1 else none
  | _, _ => none

def clauseMeet (c1 c2 : ValidClause3) : ValidClause3 :=
  ⟨varStateMeet c1.x1 c2.x1, varStateMeet c1.x2 c2.x2, varStateMeet c1.x3 c2.x3⟩

/-! ### Section II: Kernel-Verified Poset Lattice Theorems -/

/-- Total number of valid clauses on 3 Boolean variables is 3³ = 27. -/
theorem card_allValidClauses3 : allValidClauses3.length = 27 := by decide

/-- Layer 0 (empty clause / apex) contains exactly 1 element. -/
theorem layer0_count : (clausesOfRank3 0).length = 1 := by decide

/-- Layer 1 (unit clauses: x₁, ¬x₁, x₂, ¬x₂, x₃, ¬x₃) contains exactly 6 elements. -/
theorem layer1_count : (clausesOfRank3 1).length = 6 := by decide

/-- Layer 2 (2-literal clauses) contains exactly 12 elements. -/
theorem layer2_count : (clausesOfRank3 2).length = 12 := by decide

/-- Layer 3 (full 3-literal clauses / atoms of B₃) contains 2³ = 8 elements. -/
theorem layer3_count : (clausesOfRank3 3).length = 8 := by decide

/-- Rank stratification partition identity: 1 + 6 + 12 + 8 = 27 = 3³. -/
theorem layer_partition_sum_three :
    (clausesOfRank3 0).length + (clausesOfRank3 1).length +
    (clausesOfRank3 2).length + (clausesOfRank3 3).length = allValidClauses3.length := by
  decide

/-- Covering edge count of the 3-variable Conflict-Clause Hasse diagram is 54. -/
theorem coveringEdges3_count : coveringEdges3.length = 54 := by decide

/-- Covering edges stratified by layer: 6 from L₀→L₁, 24 from L₁→L₂, 24 from L₂→L₃. -/
theorem coveringEdges_by_layer :
    (coveringEdgesFromRank3 0).length = 6 ∧
    (coveringEdgesFromRank3 1).length = 24 ∧
    (coveringEdgesFromRank3 2).length = 24 ∧
    (coveringEdgesFromRank3 0).length + (coveringEdgesFromRank3 1).length +
    (coveringEdgesFromRank3 2).length = coveringEdges3.length := by
  decide

/-- Helper lemma: `varStateSub` is reflexive. -/
theorem varStateSub_refl (s : VarState) : varStateSub s s = true := by
  rcases s with _ | (_ | _) <;> rfl

/-- Helper lemma: `varStateSub` is transitive. -/
theorem varStateSub_trans (s1 s2 s3 : VarState)
    (h12 : varStateSub s1 s2 = true) (h23 : varStateSub s2 s3 = true) :
    varStateSub s1 s3 = true := by
  rcases s1 with _ | (_ | _) <;>
  rcases s2 with _ | (_ | _) <;>
  rcases s3 with _ | (_ | _) <;>
  revert h12 h23 <;> decide

/-- Helper lemma: `varStateSub` is antisymmetric. -/
theorem varStateSub_antisymm (s1 s2 : VarState)
    (h12 : varStateSub s1 s2 = true) (h21 : varStateSub s2 s1 = true) :
    s1 = s2 := by
  rcases s1 with _ | (_ | _) <;>
  rcases s2 with _ | (_ | _) <;>
  revert h12 h21 <;> decide

/-- Helper lemma: `varStateMeet` is a lower bound on the left. -/
theorem varStateMeet_sub_left (s1 s2 : VarState) :
    varStateSub (varStateMeet s1 s2) s1 = true := by
  rcases s1 with _ | (_ | _) <;>
  rcases s2 with _ | (_ | _) <;> rfl

/-- Helper lemma: `varStateMeet` is a lower bound on the right. -/
theorem varStateMeet_sub_right (s1 s2 : VarState) :
    varStateSub (varStateMeet s1 s2) s2 = true := by
  rcases s1 with _ | (_ | _) <;>
  rcases s2 with _ | (_ | _) <;> rfl

/-- Helper lemma: universal property of `varStateMeet`. -/
theorem varStateSub_meet_eq (s s1 s2 : VarState) :
    varStateSub s (varStateMeet s1 s2) = (varStateSub s s1 && varStateSub s s2) := by
  rcases s with _ | (_ | _) <;>
  rcases s1 with _ | (_ | _) <;>
  rcases s2 with _ | (_ | _) <;> rfl

/-- Characterization of `ImpliesPoset` via componentwise `varStateSub`. -/
theorem impliesPoset_iff (c1 c2 : ValidClause3) :
    ImpliesPoset c1 c2 ↔
      (varStateSub c1.x1 c2.x1 = true ∧
       varStateSub c1.x2 c2.x2 = true ∧
       varStateSub c1.x3 c2.x3 = true) := by
  unfold ImpliesPoset isImplied
  simp [Bool.and_eq_true, and_assoc]

/-- Reflexivity of the Conflict-Clause Implication Poset `(L_Φ, ≼)`. -/
theorem impliesPoset_refl (c : ValidClause3) : ImpliesPoset c c := by
  rw [impliesPoset_iff]
  exact ⟨varStateSub_refl c.x1, varStateSub_refl c.x2, varStateSub_refl c.x3⟩

/-- Transitivity of the Conflict-Clause Implication Poset `(L_Φ, ≼)`. -/
theorem impliesPoset_trans (c1 c2 c3 : ValidClause3)
    (h12 : ImpliesPoset c1 c2) (h23 : ImpliesPoset c2 c3) :
    ImpliesPoset c1 c3 := by
  rw [impliesPoset_iff] at *
  exact ⟨varStateSub_trans c1.x1 c2.x1 c3.x1 h12.1 h23.1,
         varStateSub_trans c1.x2 c2.x2 c3.x2 h12.2.1 h23.2.1,
         varStateSub_trans c1.x3 c2.x3 c3.x3 h12.2.2 h23.2.2⟩

/-- Antisymmetry of the Conflict-Clause Implication Poset `(L_Φ, ≼)`. -/
theorem impliesPoset_antisymm (c1 c2 : ValidClause3)
    (h12 : ImpliesPoset c1 c2) (h21 : ImpliesPoset c2 c1) :
    c1 = c2 := by
  rw [impliesPoset_iff] at *
  rcases c1 with ⟨x1, x2, x3⟩
  rcases c2 with ⟨y1, y2, y3⟩
  congr
  · exact varStateSub_antisymm x1 y1 h12.1 h21.1
  · exact varStateSub_antisymm x2 y2 h12.2.1 h21.2.1
  · exact varStateSub_antisymm x3 y3 h12.2.2 h21.2.2

/-- The empty clause `∅` at Layer 0 is the global minimum in subset order
    (strongest element under implication: `∅ ≼ c` for every `c`). -/
theorem emptyClause3_minimal (c : ValidClause3) : ImpliesPoset emptyClause3 c := by
  unfold ImpliesPoset isImplied emptyClause3 varStateSub
  rfl

/-- Meet (`clauseMeet`) is a lower bound on the left (`c1 ∧ c2 ≼ c1`). -/
theorem clauseMeet_implies_left (c1 c2 : ValidClause3) :
    ImpliesPoset (clauseMeet c1 c2) c1 := by
  rw [impliesPoset_iff]
  exact ⟨varStateMeet_sub_left c1.x1 c2.x1,
         varStateMeet_sub_left c1.x2 c2.x2,
         varStateMeet_sub_left c1.x3 c2.x3⟩

/-- Meet (`clauseMeet`) is a lower bound on the right (`c1 ∧ c2 ≼ c2`). -/
theorem clauseMeet_implies_right (c1 c2 : ValidClause3) :
    ImpliesPoset (clauseMeet c1 c2) c2 := by
  rw [impliesPoset_iff]
  exact ⟨varStateMeet_sub_right c1.x1 c2.x1,
         varStateMeet_sub_right c1.x2 c2.x2,
         varStateMeet_sub_right c1.x3 c2.x3⟩

/-- Universal property of the greatest lower bound (meet):
    `c ≼ clauseMeet c1 c2 ↔ c ≼ c1 ∧ c ≼ c2`. -/
theorem implies_clauseMeet_iff (c c1 c2 : ValidClause3) :
    ImpliesPoset c (clauseMeet c1 c2) ↔ (ImpliesPoset c c1 ∧ ImpliesPoset c c2) := by
  rw [impliesPoset_iff, impliesPoset_iff, impliesPoset_iff]
  unfold clauseMeet
  simp only [varStateSub_meet_eq, Bool.and_eq_true]
  constructor
  · intro ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩
    exact ⟨⟨h1a, h2a, h3a⟩, ⟨h1b, h2b, h3b⟩⟩
  · intro ⟨⟨h1a, h2a, h3a⟩, ⟨h1b, h2b, h3b⟩⟩
    exact ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩

end ConflictClauseLattice
