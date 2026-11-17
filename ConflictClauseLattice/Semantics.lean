/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Mathlib
import ConflictClauseLattice.HomologicalCertificate

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/main.tex
PAPER_SECTION: Section "Model counting by unobstructed atoms", Theorem thm:count
PAPER_SHA256: 281ce4520787c819d3184721c9d853f124307abc9be3da2c3394bc7dbc7aeec7

Locked paper claim, quoted verbatim:

PAPER_QUOTE_BEGIN
\begin{theorem}[\lean{modelCount3_eq_unobstructedAtomCount3}]\label{thm:count}
For every CNF formula $\Phi$ over $x_1,x_2,x_3$, $\#\Phi$ equals the number of rank-$3$ clauses unobstructed by $\Phi$.
\end{theorem}
PAPER_QUOTE_END

Reading of the paper's terms (from the paper's Sections "The poset $L_3$" and "Model counting"):
* a clause is a triple of variable states in `{⊥, ⊤, F}` (`Option Bool`: `none` absent,
  `some true` positive, `some false` negative); a CNF formula `Φ` is a list of clauses;
* an assignment is `α ∈ {0,1}^3` (`Bool × Bool × Bool`); `α` satisfies a clause iff one of its
  literals is true under `α`, i.e. some coordinate state equals `some αᵢ`; `#Φ` counts the
  assignments satisfying every clause of `Φ`;
* a rank-3 clause has a literal on every variable, so it is a triple of polarities
  `A ∈ Bool × Bool × Bool` (coordinate `some Aᵢ`);
* `c ≼ A` iff componentwise `cᵢ = ⊥` or `cᵢ = Aᵢ`; `A` is unobstructed iff no `c ∈ Φ` has `c ≼ A`.

`formal_claim` is the statement of `ConflictClauseLattice.modelCount3_eq_unobstructedAtomCount3`
(list-based counts over the repository's enumerations). `paper_claim` counts with `Finset.card`
over `Bool × Bool × Bool` using the definitions above. The correspondence proves the two
counting conventions agree.

Scope: a finite combinatorial identity for three variables. No claim is made about the complexity
of SAT, #SAT, P vs NP or the Exponential Time Hypothesis.
-/

namespace TruthGate

open ConflictClauseLattice

-- TRUTH-GATE LOCK BEGIN
/-- The repository's statement (`modelCount3_eq_unobstructedAtomCount3`). -/
def formal_claim : Prop :=
  ∀ Φ : List ValidClause3, modelCount3 Φ = unobstructedAtomCount3 Φ

/-- Paper Theorem thm:count: `#Φ` equals the number of rank-3 clauses unobstructed by `Φ`. -/
def paper_claim : Prop :=
  ∀ Φ : List ValidClause3,
    (Finset.univ.filter (fun α : Bool × Bool × Bool =>
        ∀ c ∈ Φ, c.x1 = some α.1 ∨ c.x2 = some α.2.1 ∨ c.x3 = some α.2.2)).card =
    (Finset.univ.filter (fun A : Bool × Bool × Bool =>
        ∀ c ∈ Φ, ¬ ((c.x1 = none ∨ c.x1 = some A.1) ∧ (c.x2 = none ∨ c.x2 = some A.2.1) ∧
          (c.x3 = none ∨ c.x3 = some A.2.2)))).card

theorem varStateSat_iff (s : Option Bool) (b : Bool) :
    varStateSat s b = true ↔ s = some b := by
  cases s <;> simp [varStateSat]

theorem varStateSub_some_iff (s : Option Bool) (b : Bool) :
    varStateSub s (some b) = true ↔ (s = none ∨ s = some b) := by
  cases s <;> simp [varStateSub]

theorem varStateSub_some_false_iff (s : Option Bool) (b : Bool) :
    varStateSub s (some b) = false ↔ ¬ (s = none ∨ s = some b) := by
  rw [← varStateSub_some_iff]
  simp

theorem allAssignments3_eq : allAssignments3 =
    [⟨false, false, false⟩, ⟨false, false, true⟩, ⟨false, true, false⟩, ⟨false, true, true⟩,
     ⟨true, false, false⟩, ⟨true, false, true⟩, ⟨true, true, false⟩, ⟨true, true, true⟩] := rfl

/-- A count over `Bool × Bool × Bool` equals the count over the repository's enumeration. -/
theorem card_filter_eq_length (P : Bool × Bool × Bool → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (allAssignments3.filter (fun α => decide (P (α.a1, α.a2, α.a3)))).length := by
  rw [← List.countP_eq_length_filter, allAssignments3_eq, Finset.card_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, List.countP_cons, List.countP_nil,
    decide_eq_true_eq]
  ring

theorem modelCount3_eq_card (Φ : List ValidClause3) :
    modelCount3 Φ = (Finset.univ.filter (fun α : Bool × Bool × Bool =>
        ∀ c ∈ Φ, c.x1 = some α.1 ∨ c.x2 = some α.2.1 ∨ c.x3 = some α.2.2)).card := by
  rw [card_filter_eq_length, modelCount3]
  congr 1
  apply List.filter_congr
  intro α _
  apply Bool.eq_iff_iff.mpr
  simp [satisfiesFormula, satisfiesClause, varStateSat_iff, or_assoc]

/-- Negating every coordinate is a bijection of `Bool × Bool × Bool`, so it preserves counts. -/
theorem card_filter_neg (P : Bool × Bool × Bool → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun x : Bool × Bool × Bool => P (!x.1, !x.2.1, !x.2.2))).card := by
  rw [Finset.card_filter, Finset.card_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.not_true, Bool.not_false]
  ring

theorem unobstructedAtomCount3_eq_card (Φ : List ValidClause3) :
    unobstructedAtomCount3 Φ = (Finset.univ.filter (fun A : Bool × Bool × Bool =>
        ∀ c ∈ Φ, ¬ ((c.x1 = none ∨ c.x1 = some A.1) ∧ (c.x2 = none ∨ c.x2 = some A.2.1) ∧
          (c.x3 = none ∨ c.x3 = some A.2.2)))).card := by
  rw [card_filter_neg, card_filter_eq_length, unobstructedAtomCount3, ← dualAtoms_eq_layer3,
    List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro α _
  apply Bool.eq_iff_iff.mpr
  simp [isUnobstructedAtom, dualAtomOfAssignment, isImplied, varStateSub_some_false_iff]
    <;> exact forall₂_congr fun c _ => by tauto

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  constructor
  · intro h Φ
    rw [← modelCount3_eq_card, ← unobstructedAtomCount3_eq_card]
    exact h Φ
  · intro h Φ
    rw [modelCount3_eq_card, unobstructedAtomCount3_eq_card]
    exact h Φ
-- TRUTH-GATE LOCK END

/-- The repository's theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim := by
  intro Φ
  exact modelCount3_eq_unobstructedAtomCount3 Φ

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
