/-
  AlphaBetaMonadic.lean
  Standalone zero-dependency Lean 4.35.0 formalization of 18 core monadic-continuation,
  reader-monad, tie-breaking, Lemma 1/2, Theorem 1 (full inductive history-dependent
  game-tree soundness), Corollary 1(a)-(b), Corollary 2 (optimal plays), and exact
  Wikipedia 36-leaf game-tree pruning theorems for:
    Martín Hötzel Escardó and Paulo Oliva, "Alpha-Beta Pruning via Monadic Continuations",
    arXiv:2611.32320 (Nov. 24, 2026).

  Author: Lluis Eriksson
  License: MIT
-/

namespace AlphaBetaMonadic

/-- Constructive, zero-warning `ite` reduction helpers. -/
private theorem ite_pos {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) :
    (if c then a else b) = a := by
  split
  · rfl
  · rename_i hneg; exact absurd h hneg

private theorem ite_neg {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬c) :
    (if c then a else b) = b := by
  split
  · rename_i hpos; exact absurd hpos h
  · rfl

/-- Outcome carrying an integer value and a play (sequence of integer moves) (Sec. 5). -/
structure Outcome where
  val : Int
  play : List Int
deriving DecidableEq, Repr

/-- First-element-preserving binary max on `Outcome` (`pickMax` of Sec. 5 / App. A):
    if `x.val ≥ y.val`, keep `x` (so a later pruned bound cannot displace an earlier optimal play). -/
def pickMax2 (x y : Outcome) : Outcome :=
  if y.val ≤ x.val then x else y

/-- First-element-preserving binary min on `Outcome` (`pickMin` of Sec. 5 / App. A). -/
def pickMin2 (x y : Outcome) : Outcome :=
  if x.val ≤ y.val then x else y

/-- Non-empty list fold for `pickMax` (`head` + `tail`). -/
def pickMax (x : Outcome) : List Outcome → Outcome
  | [] => x
  | y :: ys => pickMax (pickMax2 x y) ys

/-- Non-empty list fold for `pickMin` (`head` + `tail`). -/
def pickMin (x : Outcome) : List Outcome → Outcome
  | [] => x
  | y :: ys => pickMin (pickMin2 x y) ys

/-- Initial segment up to and including the first element satisfying `p` (Sec. 3.1 / Def. 1). -/
def takeUntil (p : Outcome → Bool) : List Outcome → List Outcome
  | [] => []
  | y :: ys => match p y with | true => [y] | false => y :: takeUntil p ys

/-- History-dependent alternating finite game tree (Sec. 6.1):
    each internal node specifies the player (`max` or `min`) and a non-empty list of child subgames
    (head child + tail children), so move sets and tree depth may vary arbitrarily by history. -/
inductive GameTree where
  | leaf (out : Outcome)
  | maxNode (first : GameTree) (rest : List GameTree)
  | minNode (first : GameTree) (rest : List GameTree)

mutual
  /-- Exhaustive minimax outcome (`out(G)` of Sec. 2 / Sec. 4). -/
  def out : GameTree → Outcome
    | GameTree.leaf o => o
    | GameTree.maxNode g gs => pickMax (out g) (outList gs)
    | GameTree.minNode g gs => pickMin (out g) (outList gs)

  /-- Exhaustive minimax mapped over child list. -/
  def outList : List GameTree → List Outcome
    | [] => []
    | g :: gs => out g :: outList gs
end

mutual
  /-- Monadic alpha-beta outcome (`out^*_{α,β}(G)` via Reader `(Int × Int)` + Continuation, Def. 1). -/
  def outAB : GameTree → Int → Int → Outcome
    | GameTree.leaf o, _, _ => o
    | GameTree.maxNode g gs, a, b =>
      let v := outAB g a b
      if b ≤ v.val then v
      else
        let a' := if a ≤ v.val then v.val else a
        pickMax v (takeUntil (fun o => decide (b ≤ o.val)) (outABListMax gs a' b))
    | GameTree.minNode g gs, a, b =>
      let v := outAB g a b
      if v.val ≤ a then v
      else
        let b' := if v.val ≤ b then v.val else b
        pickMin v (takeUntil (fun o => decide (o.val ≤ a)) (outABListMin gs a b'))

  /-- Monadic `ℓ(xs)(α, β)` list evaluation for `max` (Def. 1 / Lem. 1). -/
  def outABListMax : List GameTree → Int → Int → List Outcome
    | [], _, _ => []
    | g :: gs, a, b =>
      let v := outAB g a b
      let a' := if a ≤ v.val then v.val else a
      v :: outABListMax gs a' b

  /-- Monadic `ℓ(xs)(α, β)` list evaluation for `min` (dual Def. 1 / Lem. 1). -/
  def outABListMin : List GameTree → Int → Int → List Outcome
    | [], _, _ => []
    | g :: gs, a, b =>
      let v := outAB g a b
      let b' := if v.val ≤ b then v.val else b
      v :: outABListMin gs a b'
end

/-- Theorem 1 (Sec. 5 / App. A `pickMax` Value Characterization):
    `(pickMax x xs).val ≥ x.val` and `(pickMax x xs).val ≥ y.val` for every `y ∈ xs`,
    and `pickMax x xs` equals either `x` or some element of `xs`. -/
theorem pickMax_val_eq_max (xs : List Outcome) :
    ∀ x : Outcome,
      (x.val ≤ (pickMax x xs).val) ∧
      (∀ y, y ∈ xs → y.val ≤ (pickMax x xs).val) ∧
      (pickMax x xs = x ∨ pickMax x xs ∈ xs) := by
  induction xs with
  | nil =>
    intro x
    refine ⟨Int.le_refl x.val, ?_, Or.inl rfl⟩
    intro y hy; cases hy
  | cons z zs ih =>
    intro x
    dsimp only [pickMax]
    have hsub := ih (pickMax2 x z)
    have hx_le : x.val ≤ (pickMax2 x z).val := by
      dsimp only [pickMax2]; split
      · exact Int.le_refl _
      · omega
    have hz_le : z.val ≤ (pickMax2 x z).val := by
      dsimp only [pickMax2]; split
      · assumption
      · exact Int.le_refl _
    refine ⟨Int.le_trans hx_le hsub.1, ?_, ?_⟩
    · intro y hy
      cases hy with
      | head => exact Int.le_trans hz_le hsub.1
      | tail _ htl => exact hsub.2.1 y htl
    · cases hsub.2.2 with
      | inl heq =>
        if h : z.val ≤ x.val then
          have hpm2 : pickMax2 x z = x := by dsimp only [pickMax2]; exact ite_pos h
          exact Or.inl (heq.trans hpm2)
        else
          have hpm2 : pickMax2 x z = z := by dsimp only [pickMax2]; exact ite_neg h
          have heqz : pickMax (pickMax2 x z) zs = z := heq.trans hpm2
          rw [heqz]
          exact Or.inr List.mem_cons_self
      | inr hmem =>
        exact Or.inr (List.mem_cons_of_mem z hmem)

/-- Theorem 2 (Sec. 5 / App. A `pickMin` Value Characterization):
    Dual characterization for `pickMin`. -/
theorem pickMin_val_eq_min (xs : List Outcome) :
    ∀ x : Outcome,
      ((pickMin x xs).val ≤ x.val) ∧
      (∀ y, y ∈ xs → (pickMin x xs).val ≤ y.val) ∧
      (pickMin x xs = x ∨ pickMin x xs ∈ xs) := by
  induction xs with
  | nil =>
    intro x
    refine ⟨Int.le_refl x.val, ?_, Or.inl rfl⟩
    intro y hy; cases hy
  | cons z zs ih =>
    intro x
    dsimp only [pickMin]
    have hsub := ih (pickMin2 x z)
    have hx_ge : (pickMin2 x z).val ≤ x.val := by
      dsimp only [pickMin2]; split
      · exact Int.le_refl _
      · omega
    have hz_ge : (pickMin2 x z).val ≤ z.val := by
      dsimp only [pickMin2]; split
      · assumption
      · exact Int.le_refl _
    refine ⟨Int.le_trans hsub.1 hx_ge, ?_, ?_⟩
    · intro y hy
      cases hy with
      | head => exact Int.le_trans hsub.1 hz_ge
      | tail _ htl => exact hsub.2.1 y htl
    · cases hsub.2.2 with
      | inl heq =>
        if h : x.val ≤ z.val then
          have hpm2 : pickMin2 x z = x := by dsimp only [pickMin2]; exact ite_pos h
          exact Or.inl (heq.trans hpm2)
        else
          have hpm2 : pickMin2 x z = z := by dsimp only [pickMin2]; exact ite_neg h
          have heqz : pickMin (pickMin2 x z) zs = z := heq.trans hpm2
          rw [heqz]
          exact Or.inr List.mem_cons_self
      | inr hmem =>
        exact Or.inr (List.mem_cons_of_mem z hmem)

/-- Theorem 3 (Sec. 5 p. 13 `pickMax` First-Tie Preservation):
    If every element `y ∈ xs` satisfies `y.val ≤ x.val`, then `pickMax x xs = x` identically
    (preserving both value AND play even under ties!). -/
theorem pickMax_first_tie_preserves (xs : List Outcome) :
    ∀ x : Outcome, (∀ y, y ∈ xs → y.val ≤ x.val) → pickMax x xs = x := by
  induction xs with
  | nil => intro x _; rfl
  | cons z zs ih =>
    intro x hle
    dsimp only [pickMax, pickMax2]
    rw [ite_pos (hle z List.mem_cons_self)]
    exact ih x (fun y hy => hle y (List.mem_cons_of_mem z hy))

/-- Theorem 4 (Sec. 5 p. 13 `pickMin` First-Tie Preservation):
    If every element `y ∈ xs` satisfies `x.val ≤ y.val`, then `pickMin x xs = x` identically. -/
theorem pickMin_first_tie_preserves (xs : List Outcome) :
    ∀ x : Outcome, (∀ y, y ∈ xs → x.val ≤ y.val) → pickMin x xs = x := by
  induction xs with
  | nil => intro x _; rfl
  | cons z zs ih =>
    intro x hge
    dsimp only [pickMin, pickMin2]
    rw [ite_pos (hge z List.mem_cons_self)]
    exact ih x (fun y hy => hge y (List.mem_cons_of_mem z hy))

/-- Theorem 5 (Def. 1 `takeUntil` Non-Emptiness & Membership Preservation):
    Every element of `takeUntil p xs` belongs to `xs`, and if `xs` is non-empty so is `takeUntil p xs`. -/
theorem takeUntil_nonempty_of_nonempty (p : Outcome → Bool) (xs : List Outcome) :
    (∀ y, y ∈ takeUntil p xs → y ∈ xs) ∧ (xs ≠ [] → takeUntil p xs ≠ []) := by
  constructor
  · induction xs with
    | nil => intro y hy; exact hy
    | cons z zs ih =>
      intro y hy
      dsimp only [takeUntil] at hy
      cases hp : p z with
      | true =>
        rw [hp] at hy
        cases hy with
        | head => exact List.mem_cons_self
        | tail _ hnil => cases hnil
      | false =>
        rw [hp] at hy
        cases hy with
        | head => exact List.mem_cons_self
        | tail _ htl => exact List.mem_cons_of_mem z (ih y htl)
  · intro hne
    cases xs with
    | nil => exact absurd rfl hne
    | cons z zs =>
      dsimp only [takeUntil]
      cases p z <;> intro h <;> cases h

/-- Theorem 6 (Sec. 4 Theorem 1(iii) Key Lemma: `takeUntil` Keeps Whole List When Predicate Fails):
    If `p y = false` for every `y ∈ xs`, then `takeUntil p xs = xs`. -/
theorem takeUntil_all_false_eq_self (p : Outcome → Bool) (xs : List Outcome)
    (hfalse : ∀ y, y ∈ xs → p y = false) :
    takeUntil p xs = xs := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    dsimp only [takeUntil]
    rw [hfalse z List.mem_cons_self]
    rw [ih (fun y hy => hfalse y (List.mem_cons_of_mem z hy))]

/-- Theorem 7 (Sec. 3.1 Beta/Alpha Cutoff Immediate Termination):
    If `p y = true`, then `takeUntil p (y :: ys) = [y]`, never inspecting `ys`. -/
theorem takeUntil_head_ge_stops (p : Outcome → Bool) (y : Outcome) (ys : List Outcome)
    (h : p y = true) :
    takeUntil p (y :: ys) = [y] := by
  dsimp only [takeUntil]
  rw [h]

/-- Reader monad `T α = Env → α` (Sec. 3.1). -/
def Reader (E α : Type) := E → α
def readerPure {E α : Type} (x : α) : Reader E α := fun _ => x
def readerBind {E α β : Type} (m : Reader E α) (f : α → Reader E β) : Reader E β :=
  fun e => f (m e) e

/-- Theorem 8 (Sec. 3.1 Reader Monad Laws):
    Left identity, right identity, and associativity for `Reader E`. -/
theorem reader_monad_laws {E α β γ : Type}
    (x : α) (m : Reader E α) (f : α → Reader E β) (g : β → Reader E γ) :
    (readerBind (readerPure x) f = f x) ∧
    (readerBind m readerPure = m) ∧
    (readerBind (readerBind m f) g = readerBind m (fun a => readerBind (f a) g)) :=
  ⟨rfl, rfl, rfl⟩

/-- Continuation monad `K R α = (α → R) → R` (Sec. 2 / Sec. 3). -/
def Cont (R α : Type) := (α → R) → R
def contPure {R α : Type} (x : α) : Cont R α := fun k => k x
def contBind {R α β : Type} (m : Cont R α) (f : α → Cont R β) : Cont R β :=
  fun k => m (fun a => f a k)

/-- Theorem 9 (Sec. 2 Continuation Monad Laws):
    Left identity, right identity, and associativity for `Cont R`. -/
theorem continuation_monad_laws {R α β γ : Type}
    (x : α) (m : Cont R α) (f : α → Cont R β) (g : β → Cont R γ) :
    (contBind (contPure x) f = f x) ∧
    (contBind m contPure = m) ∧
    (contBind (contBind m f) g = contBind m (fun a => contBind (f a) g)) :=
  ⟨rfl, rfl, rfl⟩

private theorem takeUntil_captures_witness (p : Outcome → Bool) (xs : List Outcome) :
    (∃ y, y ∈ xs ∧ p y = true) → ∃ z, z ∈ takeUntil p xs ∧ p z = true := by
  induction xs with
  | nil => intro ⟨y, hy, _⟩; cases hy
  | cons w ws ih =>
    intro ⟨y, hy, hpy⟩
    dsimp only [takeUntil]
    cases hpw : p w with
    | true =>
      exact ⟨w, List.mem_cons_self, hpw⟩
    | false =>
      cases hy with
      | head => rw [hpw] at hpy; cases hpy
      | tail _ htl =>
        rcases ih ⟨y, htl, hpy⟩ with ⟨z, hz, hpz⟩
        exact ⟨z, List.mem_cons_of_mem w hz, hpz⟩

/-- Theorem 10 (Sec. 4 Lemma 2(i) for `max` — Fail-Low Preservation). -/
theorem lemma2_max_fail_low (p : Outcome → Bool) (a : Int) (x : Outcome) (xs : List Outcome)
    (hx : x.val ≤ a) (hxs : ∀ y, y ∈ xs → y.val ≤ a) :
    (pickMax x (takeUntil p xs)).val ≤ a := by
  have hpm := pickMax_val_eq_max (takeUntil p xs) x
  cases hpm.2.2 with
  | inl heq => rw [heq]; exact hx
  | inr hmem =>
    have hin := (takeUntil_nonempty_of_nonempty p xs).1 _ hmem
    exact hxs _ hin

/-- Theorem 11 (Sec. 4 Lemma 2(ii) for `max` — Beta Cutoff Preservation). -/
theorem lemma2_max_fail_high (b : Int) (x : Outcome) (xs : List Outcome)
    (hwit : ∃ y, y ∈ xs ∧ b ≤ y.val) :
    b ≤ (pickMax x (takeUntil (fun o => decide (b ≤ o.val)) xs)).val := by
  rcases hwit with ⟨y, hy, hby⟩
  have hdec : decide (b ≤ y.val) = true := decide_eq_true hby
  rcases takeUntil_captures_witness (fun o => decide (b ≤ o.val)) xs ⟨y, hy, hdec⟩ with ⟨z, hz, hpz⟩
  have hbz : b ≤ z.val := of_decide_eq_true hpz
  have hle := (pickMax_val_eq_max (takeUntil (fun o => decide (b ≤ o.val)) xs) x).2.1 z hz
  exact Int.le_trans hbz hle

/-- Theorem 12 (Sec. 4 Dual Lemma 2(i) for `min` — Fail-High Preservation). -/
theorem lemma2_min_fail_high (p : Outcome → Bool) (b : Int) (x : Outcome) (xs : List Outcome)
    (hx : b ≤ x.val) (hxs : ∀ y, y ∈ xs → b ≤ y.val) :
    b ≤ (pickMin x (takeUntil p xs)).val := by
  have hpm := pickMin_val_eq_min (takeUntil p xs) x
  cases hpm.2.2 with
  | inl heq => rw [heq]; exact hx
  | inr hmem =>
    have hin := (takeUntil_nonempty_of_nonempty p xs).1 _ hmem
    exact hxs _ hin

/-- Theorem 13 (Sec. 4 Dual Lemma 2(ii) for `min` — Alpha Cutoff Preservation). -/
theorem lemma2_min_fail_low (a : Int) (x : Outcome) (xs : List Outcome)
    (hwit : ∃ y, y ∈ xs ∧ y.val ≤ a) :
    (pickMin x (takeUntil (fun o => decide (o.val ≤ a)) xs)).val ≤ a := by
  rcases hwit with ⟨y, hy, hya⟩
  have hdec : decide (y.val ≤ a) = true := decide_eq_true hya
  rcases takeUntil_captures_witness (fun o => decide (o.val ≤ a)) xs ⟨y, hy, hdec⟩ with ⟨z, hz, hpz⟩
  have hza : z.val ≤ a := of_decide_eq_true hpz
  have hge := (pickMin_val_eq_min (takeUntil (fun o => decide (o.val ≤ a)) xs) x).2.1 z hz
  exact Int.le_trans hge hza

/-- The Escardó–Oliva Theorem 1 invariant predicate on a single `GameTree`. -/
def ABInvariant (g : GameTree) : Prop :=
  ∀ a b : Int,
    ((out g).val ≤ a → (outAB g a b).val ≤ a) ∧
    (b ≤ (out g).val → b ≤ (outAB g a b).val) ∧
    (a < (out g).val → (out g).val < b → outAB g a b = out g)

private theorem mem_outList_exists (ts : List GameTree) (o : Outcome) (h : o ∈ outList ts) :
    ∃ t, t ∈ ts ∧ out t = o := by
  induction ts with
  | nil => cases h
  | cons t ts' ih =>
    dsimp only [outList] at h
    cases h with
    | head => exact ⟨t, List.mem_cons_self, rfl⟩
    | tail _ htl =>
      rcases ih htl with ⟨t', ht', heq⟩
      exact ⟨t', List.mem_cons_of_mem t ht', heq⟩

private theorem mem_outList_of_mem (ts : List GameTree) (t : GameTree) (h : t ∈ ts) :
    out t ∈ outList ts := by
  induction ts with
  | nil => cases h
  | cons x xs ih =>
    dsimp only [outList]
    cases h with
    | head => exact List.mem_cons_self
    | tail _ htl => exact List.mem_cons_of_mem (out x) (ih htl)

private theorem pickMax_indep_of_le (a : Int) (ys : List Outcome) :
    ∀ u w : Outcome, u.val ≤ a → w.val ≤ a → a < (pickMax w ys).val → pickMax u ys = pickMax w ys := by
  induction ys with
  | nil => intro u w _ hw hgt; dsimp only [pickMax] at hgt; omega
  | cons z zs ih =>
    intro u w hu hw hgt
    dsimp only [pickMax] at hgt ⊢
    if hz : a < z.val then
      dsimp only [pickMax2]
      rw [ite_neg (by omega), ite_neg (by omega)]
    else
      have hu' : (pickMax2 u z).val ≤ a := by
        dsimp only [pickMax2]; split
        · exact hu
        · omega
      have hw' : (pickMax2 w z).val ≤ a := by
        dsimp only [pickMax2]; split
        · exact hw
        · omega
      exact ih (pickMax2 u z) (pickMax2 w z) hu' hw' hgt

private theorem pickMin_indep_of_ge (b : Int) (ys : List Outcome) :
    ∀ u w : Outcome, b ≤ u.val → b ≤ w.val → (pickMin w ys).val < b → pickMin u ys = pickMin w ys := by
  induction ys with
  | nil => intro u w _ hw hlt; dsimp only [pickMin] at hlt; omega
  | cons z zs ih =>
    intro u w hu hw hlt
    dsimp only [pickMin] at hlt ⊢
    if hz : z.val < b then
      dsimp only [pickMin2]
      rw [ite_neg (by omega), ite_neg (by omega)]
    else
      have hu' : b ≤ (pickMin2 u z).val := by
        dsimp only [pickMin2]; split
        · exact hu
        · omega
      have hw' : b ≤ (pickMin2 w z).val := by
        dsimp only [pickMin2]; split
        · exact hw
        · omega
      exact ih (pickMin2 u z) (pickMin2 w z) hu' hw' hlt

private theorem max_list_fail_low (gs : List GameTree) (hIH : ∀ g, g ∈ gs → ABInvariant g)
    (a b : Int) (hall : ∀ g, g ∈ gs → (out g).val ≤ a) :
    ∀ y, y ∈ outABListMax gs a b → y.val ≤ a := by
  induction gs with
  | nil => intro y hy; cases hy
  | cons g rest ih =>
    intro y hy
    dsimp only [outABListMax] at hy
    have hg_le : (out g).val ≤ a := hall g List.mem_cons_self
    have hv_le : (outAB g a b).val ≤ a := (hIH g List.mem_cons_self a b).1 hg_le
    have ha'_eq : (if a ≤ (outAB g a b).val then (outAB g a b).val else a) = a := by
      split
      · omega
      · rfl
    rw [ha'_eq] at hy
    cases hy with
    | head => exact hv_le
    | tail _ htl =>
      exact ih (fun x hx => hIH x (List.mem_cons_of_mem g hx))
        (fun x hx => hall x (List.mem_cons_of_mem g hx)) y htl

private theorem max_list_fail_high (gs : List GameTree) (hIH : ∀ g, g ∈ gs → ABInvariant g) :
    ∀ (a b : Int), (∃ g, g ∈ gs ∧ b ≤ (out g).val) →
      ∃ y, y ∈ outABListMax gs a b ∧ b ≤ y.val := by
  induction gs with
  | nil => intro _ _ ⟨g, hg, _⟩; cases hg
  | cons g rest ih =>
    intro a b ⟨w, hw, hbw⟩
    dsimp only [outABListMax]
    cases hw with
    | head =>
      exact ⟨outAB g a b, List.mem_cons_self, (hIH g List.mem_cons_self a b).2.1 hbw⟩
    | tail _ htl =>
      let a' := if a ≤ (outAB g a b).val then (outAB g a b).val else a
      rcases ih (fun x hx => hIH x (List.mem_cons_of_mem g hx)) a' b ⟨w, htl, hbw⟩ with ⟨y, hy, hby⟩
      exact ⟨y, List.mem_cons_of_mem _ hy, hby⟩

private theorem max_list_exact (gs : List GameTree) (hIH : ∀ g, g ∈ gs → ABInvariant g) :
    ∀ (best : Outcome) (a b : Int),
      best.val < b →
      (∀ g, g ∈ gs → (out g).val < b) →
      (best.val ≤ a ∧ a < (pickMax best (outList gs)).val ∨ a = best.val) →
      (∀ y, y ∈ outABListMax gs a b → y.val < b) ∧
      pickMax best (outABListMax gs a b) = pickMax best (outList gs) := by
  induction gs with
  | nil =>
    intro best a b _ _ _
    constructor
    · intro y hy; cases hy
    · rfl
  | cons g rest ih =>
    intro best a b hbest_lt hall hrel
    have hgb : (out g).val < b := hall g List.mem_cons_self
    have hrest_b : ∀ x, x ∈ rest → (out x).val < b := fun x hx => hall x (List.mem_cons_of_mem g hx)
    have hIH_g := hIH g List.mem_cons_self a b
    have hIH_r : ∀ x, x ∈ rest → ABInvariant x := fun x hx => hIH x (List.mem_cons_of_mem g hx)
    dsimp only [outABListMax, outList, pickMax]
    if hga : (out g).val ≤ a then
      have hv_le_a : (outAB g a b).val ≤ a := hIH_g.1 hga
      have ha_lt_b : a < b := by
        cases hrel with
        | inl h1 =>
          have hpm := pickMax_val_eq_max (outList (g :: rest)) best
          have hpm_lt_b : (pickMax best (outList (g :: rest))).val < b := by
            cases hpm.2.2 with
            | inl heq => rw [heq]; exact hbest_lt
            | inr hmem =>
              rcases mem_outList_exists (g :: rest) _ hmem with ⟨t, ht, hteq⟩
              rw [← hteq]; exact hall t ht
          omega
        | inr h2 => omega
      have hv_lt_b : (outAB g a b).val < b := by omega
      have ha'_eq : (if a ≤ (outAB g a b).val then (outAB g a b).val else a) = a := by
        split <;> omega
      rw [ha'_eq]
      cases hrel with
      | inl h1 =>
        have hbest1_le_a : (pickMax2 best (outAB g a b)).val ≤ a := by
          dsimp only [pickMax2]; split
          · exact h1.1
          · exact hv_le_a
        have hbest2_le_a : (pickMax2 best (out g)).val ≤ a := by
          dsimp only [pickMax2]; split
          · exact h1.1
          · exact hga
        have hfinal_gt_a : a < (pickMax (pickMax2 best (out g)) (outList rest)).val := h1.2
        have hsub := ih hIH_r (pickMax2 best (out g)) a b (by omega) hrest_b (Or.inl ⟨hbest2_le_a, hfinal_gt_a⟩)
        refine ⟨?_, ?_⟩
        · intro y hy
          cases hy with
          | head => exact hv_lt_b
          | tail _ htl => exact hsub.1 y htl
        · rw [pickMax_indep_of_le a (outABListMax rest a b) (pickMax2 best (outAB g a b))
              (pickMax2 best (out g)) hbest1_le_a hbest2_le_a (by rw [hsub.2]; exact hfinal_gt_a)]
          exact hsub.2
      | inr ha_eq_best =>
        have hp1 : pickMax2 best (outAB g a b) = best := by
          dsimp only [pickMax2]; exact ite_pos (by omega)
        have hp2 : pickMax2 best (out g) = best := by
          dsimp only [pickMax2]; exact ite_pos (by omega)
        rw [hp1, hp2]
        have hsub := ih hIH_r best a b hbest_lt hrest_b (Or.inr ha_eq_best)
        refine ⟨?_, hsub.2⟩
        intro y hy
        cases hy with
        | head => exact hv_lt_b
        | tail _ htl => exact hsub.1 y htl
    else
      have ha_lt_g : a < (out g).val := by omega
      have hv_eq : outAB g a b = out g := hIH_g.2.2 ha_lt_g hgb
      rw [hv_eq]
      have ha'_eq : (if a ≤ (out g).val then (out g).val else a) = (out g).val := ite_pos (by omega)
      rw [ha'_eq]
      have hbest_lt_g : best.val < (out g).val := by
        cases hrel with
        | inl h1 => omega
        | inr h2 => omega
      have hpick_eq : pickMax2 best (out g) = out g := by
        dsimp only [pickMax2]; exact ite_neg (by omega)
      rw [hpick_eq]
      have hsub := ih hIH_r (out g) (out g).val b hgb hrest_b (Or.inr rfl)
      refine ⟨?_, hsub.2⟩
      intro y hy
      cases hy with
      | head => exact hgb
      | tail _ htl => exact hsub.1 y htl

private theorem min_list_fail_high (gs : List GameTree) (hIH : ∀ g, g ∈ gs → ABInvariant g)
    (a b : Int) (hall : ∀ g, g ∈ gs → b ≤ (out g).val) :
    ∀ y, y ∈ outABListMin gs a b → b ≤ y.val := by
  induction gs with
  | nil => intro y hy; cases hy
  | cons g rest ih =>
    intro y hy
    dsimp only [outABListMin] at hy
    have hg_ge : b ≤ (out g).val := hall g List.mem_cons_self
    have hv_ge : b ≤ (outAB g a b).val := (hIH g List.mem_cons_self a b).2.1 hg_ge
    have hb'_eq : (if (outAB g a b).val ≤ b then (outAB g a b).val else b) = b := by
      split <;> omega
    rw [hb'_eq] at hy
    cases hy with
    | head => exact hv_ge
    | tail _ htl =>
      exact ih (fun x hx => hIH x (List.mem_cons_of_mem g hx))
        (fun x hx => hall x (List.mem_cons_of_mem g hx)) y htl

private theorem min_list_fail_low (gs : List GameTree) (hIH : ∀ g, g ∈ gs → ABInvariant g) :
    ∀ (a b : Int), (∃ g, g ∈ gs ∧ (out g).val ≤ a) →
      ∃ y, y ∈ outABListMin gs a b ∧ y.val ≤ a := by
  induction gs with
  | nil => intro _ _ ⟨g, hg, _⟩; cases hg
  | cons g rest ih =>
    intro a b ⟨w, hw, hwa⟩
    dsimp only [outABListMin]
    cases hw with
    | head =>
      exact ⟨outAB g a b, List.mem_cons_self, (hIH g List.mem_cons_self a b).1 hwa⟩
    | tail _ htl =>
      let b' := if (outAB g a b).val ≤ b then (outAB g a b).val else b
      rcases ih (fun x hx => hIH x (List.mem_cons_of_mem g hx)) a b' ⟨w, htl, hwa⟩ with ⟨y, hy, hya⟩
      exact ⟨y, List.mem_cons_of_mem _ hy, hya⟩

private theorem min_list_exact (gs : List GameTree) (hIH : ∀ g, g ∈ gs → ABInvariant g) :
    ∀ (best : Outcome) (a b : Int),
      a < best.val →
      (∀ g, g ∈ gs → a < (out g).val) →
      ((b ≤ best.val ∧ (pickMin best (outList gs)).val < b) ∨ b = best.val) →
      (∀ y, y ∈ outABListMin gs a b → a < y.val) ∧
      pickMin best (outABListMin gs a b) = pickMin best (outList gs) := by
  induction gs with
  | nil =>
    intro best a b _ _ _
    constructor
    · intro y hy; cases hy
    · rfl
  | cons g rest ih =>
    intro best a b hbest_gt hall hrel
    have hga : a < (out g).val := hall g List.mem_cons_self
    have hrest_a : ∀ x, x ∈ rest → a < (out x).val := fun x hx => hall x (List.mem_cons_of_mem g hx)
    have hIH_g := hIH g List.mem_cons_self a b
    have hIH_r : ∀ x, x ∈ rest → ABInvariant x := fun x hx => hIH x (List.mem_cons_of_mem g hx)
    dsimp only [outABListMin, outList, pickMin]
    if hgb : b ≤ (out g).val then
      have hv_ge_b : b ≤ (outAB g a b).val := hIH_g.2.1 hgb
      have ha_lt_b : a < b := by
        cases hrel with
        | inl h1 =>
          have hpm := pickMin_val_eq_min (outList (g :: rest)) best
          have hpm_gt_a : a < (pickMin best (outList (g :: rest))).val := by
            cases hpm.2.2 with
            | inl heq => rw [heq]; exact hbest_gt
            | inr hmem =>
              rcases mem_outList_exists (g :: rest) _ hmem with ⟨t, ht, hteq⟩
              rw [← hteq]; exact hall t ht
          omega
        | inr h2 => omega
      have hv_gt_a : a < (outAB g a b).val := by omega
      have hb'_eq : (if (outAB g a b).val ≤ b then (outAB g a b).val else b) = b := by
        split <;> omega
      rw [hb'_eq]
      cases hrel with
      | inl h1 =>
        have hbest1_ge_b : b ≤ (pickMin2 best (outAB g a b)).val := by
          dsimp only [pickMin2]; split
          · exact h1.1
          · exact hv_ge_b
        have hbest2_ge_b : b ≤ (pickMin2 best (out g)).val := by
          dsimp only [pickMin2]; split
          · exact h1.1
          · exact hgb
        have hfinal_lt_b : (pickMin (pickMin2 best (out g)) (outList rest)).val < b := h1.2
        have hsub := ih hIH_r (pickMin2 best (out g)) a b (by omega) hrest_a (Or.inl ⟨hbest2_ge_b, hfinal_lt_b⟩)
        refine ⟨?_, ?_⟩
        · intro y hy
          cases hy with
          | head => exact hv_gt_a
          | tail _ htl => exact hsub.1 y htl
        · rw [pickMin_indep_of_ge b (outABListMin rest a b) (pickMin2 best (outAB g a b))
              (pickMin2 best (out g)) hbest1_ge_b hbest2_ge_b (by rw [hsub.2]; exact hfinal_lt_b)]
          exact hsub.2
      | inr hb_eq_best =>
        have hp1 : pickMin2 best (outAB g a b) = best := by
          dsimp only [pickMin2]; exact ite_pos (by omega)
        have hp2 : pickMin2 best (out g) = best := by
          dsimp only [pickMin2]; exact ite_pos (by omega)
        rw [hp1, hp2]
        have hsub := ih hIH_r best a b hbest_gt hrest_a (Or.inr hb_eq_best)
        refine ⟨?_, hsub.2⟩
        intro y hy
        cases hy with
        | head => exact hv_gt_a
        | tail _ htl => exact hsub.1 y htl
    else
      have hg_lt_b : (out g).val < b := by omega
      have hv_eq : outAB g a b = out g := hIH_g.2.2 hga hg_lt_b
      rw [hv_eq]
      have hb'_eq : (if (out g).val ≤ b then (out g).val else b) = (out g).val := ite_pos (by omega)
      rw [hb'_eq]
      have hg_lt_best : (out g).val < best.val := by
        cases hrel with
        | inl h1 => omega
        | inr h2 => omega
      have hpick_eq : pickMin2 best (out g) = out g := by
        dsimp only [pickMin2]; exact ite_neg (by omega)
      rw [hpick_eq]
      have hsub := ih hIH_r (out g) a (out g).val hga hrest_a (Or.inr rfl)
      refine ⟨?_, hsub.2⟩
      intro y hy
      cases hy with
      | head => exact hga
      | tail _ htl => exact hsub.1 y htl

mutual
  /-- Theorem 14 (Escardó–Oliva Theorem 1 — Full Inductive Soundness on History-Dependent Game Trees):
      For EVERY finite history-dependent game tree `G` and EVERY window `(α, β)`:
      (i) `out(G).val ≤ α → outAB(G, α, β).val ≤ α`;
      (ii) `β ≤ out(G).val → β ≤ outAB(G, α, β).val`;
      (iii) `α < out(G).val ∧ out(G).val < β → outAB(G, α, β) = out(G)` (both value AND optimal play!). -/
  theorem theorem1_alphabeta_soundness : ∀ G : GameTree, ABInvariant G
    | GameTree.leaf o => fun a b => by
      dsimp only [out, outAB]
      exact ⟨fun h => h, fun h => h, fun _ _ => rfl⟩
    | GameTree.maxNode g gs => fun a b => by
      have hIH_g : ABInvariant g := theorem1_alphabeta_soundness g
      have hIH_gs : ∀ x, x ∈ gs → ABInvariant x := theorem1_list gs
      dsimp only [out, outAB]
      have hpm := pickMax_val_eq_max (outList gs) (out g)
      refine ⟨?_, ?_, ?_⟩
      · intro hle
        have hg_le : (out g).val ≤ a := Int.le_trans hpm.1 hle
        have hv_le : (outAB g a b).val ≤ a := (hIH_g a b).1 hg_le
        have hgs_le : ∀ t, t ∈ gs → (out t).val ≤ a := fun t ht =>
          Int.le_trans (hpm.2.1 (out t) (mem_outList_of_mem gs t ht)) hle
        if hbv : b ≤ (outAB g a b).val then
          rw [ite_pos hbv]; exact hv_le
        else
          rw [ite_neg hbv]
          have ha'_eq : (if a ≤ (outAB g a b).val then (outAB g a b).val else a) = a := by
            split <;> omega
          rw [ha'_eq]
          exact lemma2_max_fail_low _ a (outAB g a b) (outABListMax gs a b) hv_le
            (max_list_fail_low gs hIH_gs a b hgs_le)
      · intro hge
        if hbv : b ≤ (outAB g a b).val then
          rw [ite_pos hbv]; exact hbv
        else
          rw [ite_neg hbv]
          cases hpm.2.2 with
          | inl heq =>
            rw [heq] at hge
            exact absurd ((hIH_g a b).2.1 hge) hbv
          | inr hmem =>
            rcases mem_outList_exists gs _ hmem with ⟨w, hw, hweq⟩
            rw [← hweq] at hge
            let a' := if a ≤ (outAB g a b).val then (outAB g a b).val else a
            exact lemma2_max_fail_high b (outAB g a b) (outABListMax gs a' b)
              (max_list_fail_high gs hIH_gs a' b ⟨w, hw, hge⟩)
      · intro ha_lt hlt_b
        have hg_lt_b : (out g).val < b := Int.lt_of_le_of_lt hpm.1 hlt_b
        have hgs_lt_b : ∀ t, t ∈ gs → (out t).val < b := fun t ht =>
          Int.lt_of_le_of_lt (hpm.2.1 (out t) (mem_outList_of_mem gs t ht)) hlt_b
        if hga : (out g).val ≤ a then
          have hv_le : (outAB g a b).val ≤ a := (hIH_g a b).1 hga
          rw [ite_neg (by omega)]
          have ha'_eq : (if a ≤ (outAB g a b).val then (outAB g a b).val else a) = a := by
            split <;> omega
          rw [ha'_eq]
          have hsub := max_list_exact gs hIH_gs (out g) a b hg_lt_b hgs_lt_b (Or.inl ⟨hga, ha_lt⟩)
          have htake : takeUntil (fun o => decide (b ≤ o.val)) (outABListMax gs a b) = outABListMax gs a b :=
            takeUntil_all_false_eq_self _ _ (fun y hy => decide_eq_false (by have := hsub.1 y hy; omega))
          rw [htake]
          rw [pickMax_indep_of_le a (outABListMax gs a b) (outAB g a b) (out g) hv_le hga (by rw [hsub.2]; exact ha_lt)]
          exact hsub.2
        else
          have ha_lt_g : a < (out g).val := by omega
          have hv_eq : outAB g a b = out g := (hIH_g a b).2.2 ha_lt_g hg_lt_b
          rw [hv_eq]
          rw [ite_neg (by omega)]
          have ha'_eq : (if a ≤ (out g).val then (out g).val else a) = (out g).val := ite_pos (by omega)
          rw [ha'_eq]
          have hsub := max_list_exact gs hIH_gs (out g) (out g).val b hg_lt_b hgs_lt_b (Or.inr rfl)
          have htake : takeUntil (fun o => decide (b ≤ o.val)) (outABListMax gs (out g).val b) =
              outABListMax gs (out g).val b :=
            takeUntil_all_false_eq_self _ _ (fun y hy => decide_eq_false (by have := hsub.1 y hy; omega))
          rw [htake]
          exact hsub.2
    | GameTree.minNode g gs => fun a b => by
      have hIH_g : ABInvariant g := theorem1_alphabeta_soundness g
      have hIH_gs : ∀ x, x ∈ gs → ABInvariant x := theorem1_list gs
      dsimp only [out, outAB]
      have hpm := pickMin_val_eq_min (outList gs) (out g)
      refine ⟨?_, ?_, ?_⟩
      · intro hle
        if hva : (outAB g a b).val ≤ a then
          rw [ite_pos hva]; exact hva
        else
          rw [ite_neg hva]
          cases hpm.2.2 with
          | inl heq =>
            rw [heq] at hle
            exact absurd ((hIH_g a b).1 hle) hva
          | inr hmem =>
            rcases mem_outList_exists gs _ hmem with ⟨w, hw, hweq⟩
            rw [← hweq] at hle
            let b' := if (outAB g a b).val ≤ b then (outAB g a b).val else b
            exact lemma2_min_fail_low a (outAB g a b) (outABListMin gs a b')
              (min_list_fail_low gs hIH_gs a b' ⟨w, hw, hle⟩)
      · intro hge
        have hg_ge : b ≤ (out g).val := Int.le_trans hge hpm.1
        have hv_ge : b ≤ (outAB g a b).val := (hIH_g a b).2.1 hg_ge
        have hgs_ge : ∀ t, t ∈ gs → b ≤ (out t).val := fun t ht =>
          Int.le_trans hge (hpm.2.1 (out t) (mem_outList_of_mem gs t ht))
        if hva : (outAB g a b).val ≤ a then
          rw [ite_pos hva]; exact hv_ge
        else
          rw [ite_neg hva]
          have hb'_eq : (if (outAB g a b).val ≤ b then (outAB g a b).val else b) = b := by
            split <;> omega
          rw [hb'_eq]
          exact lemma2_min_fail_high _ b (outAB g a b) (outABListMin gs a b) hv_ge
            (min_list_fail_high gs hIH_gs a b hgs_ge)
      · intro ha_lt hlt_b
        have hg_gt_a : a < (out g).val := Int.lt_of_lt_of_le ha_lt hpm.1
        have hgs_gt_a : ∀ t, t ∈ gs → a < (out t).val := fun t ht =>
          Int.lt_of_lt_of_le ha_lt (hpm.2.1 (out t) (mem_outList_of_mem gs t ht))
        if hgb : b ≤ (out g).val then
          have hv_ge : b ≤ (outAB g a b).val := (hIH_g a b).2.1 hgb
          rw [ite_neg (by omega)]
          have hb'_eq : (if (outAB g a b).val ≤ b then (outAB g a b).val else b) = b := by
            split <;> omega
          rw [hb'_eq]
          have hsub := min_list_exact gs hIH_gs (out g) a b hg_gt_a hgs_gt_a (Or.inl ⟨hgb, hlt_b⟩)
          have htake : takeUntil (fun o => decide (o.val ≤ a)) (outABListMin gs a b) = outABListMin gs a b :=
            takeUntil_all_false_eq_self _ _ (fun y hy => decide_eq_false (by have := hsub.1 y hy; omega))
          rw [htake]
          rw [pickMin_indep_of_ge b (outABListMin gs a b) (outAB g a b) (out g) hv_ge hgb (by rw [hsub.2]; exact hlt_b)]
          exact hsub.2
        else
          have hg_lt_b : (out g).val < b := by omega
          have hv_eq : outAB g a b = out g := (hIH_g a b).2.2 hg_gt_a hg_lt_b
          rw [hv_eq]
          rw [ite_neg (by omega)]
          have hb'_eq : (if (out g).val ≤ b then (out g).val else b) = (out g).val := ite_pos (by omega)
          rw [hb'_eq]
          have hsub := min_list_exact gs hIH_gs (out g) a (out g).val hg_gt_a hgs_gt_a (Or.inr rfl)
          have htake : takeUntil (fun o => decide (o.val ≤ a)) (outABListMin gs a (out g).val) =
              outABListMin gs a (out g).val :=
            takeUntil_all_false_eq_self _ _ (fun y hy => decide_eq_false (by have := hsub.1 y hy; omega))
          rw [htake]
          exact hsub.2

  private theorem theorem1_list : ∀ (gs : List GameTree), ∀ x, x ∈ gs → ABInvariant x
    | [], _, h => by cases h
    | g :: rest, x, h => by
      cases h with
      | head => exact theorem1_alphabeta_soundness g
      | tail _ htl => exact theorem1_list rest x htl
end

mutual
  /-- Leaf predicate: `x` is one of the terminal outcomes of `G`. -/
  def isLeafOutcome : GameTree → Outcome → Prop
    | GameTree.leaf o, x => x = o
    | GameTree.maxNode g gs, x => isLeafOutcome g x ∨ isLeafOutcomeList gs x
    | GameTree.minNode g gs, x => isLeafOutcome g x ∨ isLeafOutcomeList gs x

  /-- Leaf predicate lifted to a list of child subgames. -/
  def isLeafOutcomeList : List GameTree → Outcome → Prop
    | [], _ => False
    | g :: gs, x => isLeafOutcome g x ∨ isLeafOutcomeList gs x
end

mutual
  private theorem out_is_leaf : ∀ G : GameTree, isLeafOutcome G (out G)
    | GameTree.leaf _ => rfl
    | GameTree.maxNode g gs => by
      dsimp only [out, isLeafOutcome]
      have hpm := pickMax_val_eq_max (outList gs) (out g)
      cases hpm.2.2 with
      | inl heq => rw [heq]; exact Or.inl (out_is_leaf g)
      | inr hmem => exact Or.inr (outList_is_leaf gs _ hmem)
    | GameTree.minNode g gs => by
      dsimp only [out, isLeafOutcome]
      have hpm := pickMin_val_eq_min (outList gs) (out g)
      cases hpm.2.2 with
      | inl heq => rw [heq]; exact Or.inl (out_is_leaf g)
      | inr hmem => exact Or.inr (outList_is_leaf gs _ hmem)

  private theorem outList_is_leaf : ∀ (gs : List GameTree) (x : Outcome), x ∈ outList gs → isLeafOutcomeList gs x
    | [], _, h => by cases h
    | g :: gs, x, h => by
      dsimp only [outList] at h
      dsimp only [isLeafOutcomeList]
      cases h with
      | head => exact Or.inl (out_is_leaf g)
      | tail _ htl => exact Or.inr (outList_is_leaf gs x htl)
end

/-- Theorem 15 (Escardó–Oliva Corollary 1(a) — Strict Global Bounds):
    If every leaf `o` of `G` satisfies `α < o.val < β`, then `outAB G α β = out G`. -/
theorem corollary1a_strict_global_bounds (G : GameTree) (a b : Int)
    (hbounds : ∀ o, isLeafOutcome G o → a < o.val ∧ o.val < b) :
    outAB G a b = out G := by
  have hleaf := hbounds (out G) (out_is_leaf G)
  exact (theorem1_alphabeta_soundness G a b).2.2 hleaf.1 hleaf.2

/-- Theorem 16 (Escardó–Oliva Corollary 1(b) — In-Window Exactness, Used for Tic-Tac-Toe `(-1, 1)`):
    If the computed monadic outcome lies strictly inside `(α, β)` (i.e. `α < (outAB G α β).val < β`),
    then `outAB G α β = out G` EVEN IF some leaves equal `α` or `β`! -/
theorem corollary1b_in_window_exactness (G : GameTree) (a b : Int)
    (hlo : a < (outAB G a b).val) (hhi : (outAB G a b).val < b) :
    outAB G a b = out G := by
  have hthm := theorem1_alphabeta_soundness G a b
  have hnot_lo : ¬((out G).val ≤ a) := fun h => by have := hthm.1 h; omega
  have hnot_hi : ¬(b ≤ (out G).val) := fun h => by have := hthm.2.1 h; omega
  exact hthm.2.2 (by omega) (by omega)

/-- Theorem 17 (Escardó–Oliva Corollary 2 — Optimal Play Extraction):
    Whenever `α < (out G).val < β`, the monadic continuation alpha-beta outcome `outAB G α β`
    returns BOTH the exact optimal value AND the exact first optimal play of `G` (a leaf of `G`). -/
theorem corollary2_optimal_play_soundness (G : GameTree) (a b : Int)
    (hlo : a < (out G).val) (hhi : (out G).val < b) :
    (outAB G a b).val = (out G).val ∧
    (outAB G a b).play = (out G).play ∧
    isLeafOutcome G (outAB G a b) := by
  have heq : outAB G a b = out G := (theorem1_alphabeta_soundness G a b).2.2 hlo hhi
  rw [heq]
  exact ⟨rfl, rfl, out_is_leaf G⟩

/-- Exact Wikipedia 36-leaf game tree from Escardó & Oliva Sec. 2.2 / 3.3 / 5 (Fig. 1). -/
def wikiTree : GameTree :=
  let lf (v : Int) (p : List Int) := GameTree.leaf ⟨v, p⟩
  let b00 := GameTree.maxNode
    (GameTree.minNode (lf 5 [0,0,0,0]) [lf 6 [0,0,0,1], lf 6 [0,0,0,2]])
    [GameTree.minNode (lf 7 [0,0,1,0]) [lf 4 [0,0,1,1], lf 5 [0,0,1,2]]]
  let b01 := GameTree.maxNode
    (GameTree.minNode (lf 3 [0,1,0,0]) [lf 3 [0,1,0,1], lf 3 [0,1,0,2]])
    [GameTree.minNode (lf 3 [0,1,1,0]) [lf 3 [0,1,1,1], lf 3 [0,1,1,2]]]
  let b10 := GameTree.maxNode
    (GameTree.minNode (lf 6 [1,0,0,0]) [lf 6 [1,0,0,1], lf 6 [1,0,0,2]])
    [GameTree.minNode (lf 6 [1,0,1,0]) [lf 9 [1,0,1,1], lf 9 [1,0,1,2]]]
  let b11 := GameTree.maxNode
    (GameTree.minNode (lf 7 [1,1,0,0]) [lf 7 [1,1,0,1], lf 7 [1,1,0,2]])
    [GameTree.minNode (lf 7 [1,1,1,0]) [lf 7 [1,1,1,1], lf 7 [1,1,1,2]]]
  let b20 := GameTree.maxNode
    (GameTree.minNode (lf 5 [2,0,0,0]) [lf 5 [2,0,0,1], lf 5 [2,0,0,2]])
    [GameTree.minNode (lf 5 [2,0,1,0]) [lf 5 [2,0,1,1], lf 5 [2,0,1,2]]]
  let b21 := GameTree.maxNode
    (GameTree.minNode (lf 9 [2,1,0,0]) [lf 9 [2,1,0,1], lf 9 [2,1,0,2]])
    [GameTree.minNode (lf 9 [2,1,1,0]) [lf 9 [2,1,1,1], lf 9 [2,1,1,2]]]
  GameTree.maxNode
    (GameTree.minNode b00 [b01])
    [GameTree.minNode b10 [b11], GameTree.minNode b20 [b21]]

/-- Theorem 18 (Sec. 2.2, 3.3, 5 Exact Verification of the 36-Leaf Example Game Tree):
    Both exhaustive minimax `out wikiTree` and monadic alpha-beta `outAB wikiTree (-1000) 1000`
    evaluate identically to `⟨6, [1, 0, 0, 0]⟩`, matching Escardó & Oliva p. 14 verbatim! -/
theorem wikipedia_example_tree_exact_pruning :
    out wikiTree = ⟨6, [1, 0, 0, 0]⟩ ∧
    outAB wikiTree (-1000) 1000 = ⟨6, [1, 0, 0, 0]⟩ := by
  decide

end AlphaBetaMonadic
