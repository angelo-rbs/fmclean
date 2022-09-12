
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros hp notp,
  contradiction,

end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro notnotp,
  -- usa LEM
  
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  sorry,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro PouQ,
  cases PouQ with hp hq,

  right,
  exact hp,

  left,
  exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro PandQ,
  cases PandQ with hp hq,

  split,
  exact hq,
  exact hp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro notPorQ,
  cases notPorQ with notp q,

  intro p,
  contradiction,

  intro p,
  exact q,

end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro PorQ,
  cases PorQ with p q,

  intro notp,
  contradiction,

  intro notq,
  exact q,

end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro PthenQ,
  intro notQ,
  intro p,
  
  have q : Q := PthenQ p,
  contradiction

end

theorem impl_as_contrapositive_converse : -- feitiço
  (¬Q → ¬P) → (P → Q)  :=
begin
  
  intro notQthennotP,
  intro p,

  by_cases h: Q,
  exact h,

  have notP : ¬P := notQthennotP h,
  contradiction,

end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  exact impl_as_contrapositive P Q,
  exact impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro notlem,
  apply notlem, -- pois notlem <==> (lem => boom); troca alvo
  right,
  intro p,
  apply notlem,
  left,
  exact p,

end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro first,
  intro notp,
  apply notp,
  apply first,
  intro p,
  contradiction,

end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro PorQ,
  cases PorQ with p q,

  intro npANDnq,
  cases npANDnq with np nq,
  contradiction,

  intro npANDnq,
  cases npANDnq with np nq,
  contradiction,
  
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro pandq,
  intro npornq,
  cases pandq with p q,

  cases npornq,

  contradiction,
  contradiction,

end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro notPorQ,
  split,

  intro p,
  apply notPorQ,
  left,
  exact p,
  
  intro q,
  apply notPorQ,
  right,
  exact q,

end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro h,
  cases h with np nq,
  intro porq,

  cases porq with p q,
  contradiction,
  contradiction,

end

theorem demorgan_conj : -- feitiço
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro h,
  

end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro notqORnotp,
  intro notPandQ,
  cases notPandQ with p q,
  cases notqORnotp with notq or notp,
  contradiction,
  contradiction,

end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  exact demorgan_conj P Q,
  exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  exact demorgan_disj P Q,
  exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  cases h with p QorR,
  cases QorR with q r,
  
  left,
  split,
    exact p,
    exact q,

  right,
  split,
    exact p,
    exact r,
  
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  split,

  cases h with l r,
    exact l.left,
    exact r.left,
  
  cases h with l r,
    left,
    exact l.right,

    right,
    exact r.right,

end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  split,

  cases h with p QandR,
    left,
    exact p,

    right,
    exact QandR.left,

  cases h with p QandR,
    left,
    exact p,

    right,
    exact QandR.right,

end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  
  cases h with l r,
  cases r with p r,
  left,
  exact p,
  cases l with p q,
  left,
  exact p,
  right,
  split,
  exact q,
  exact r,

end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro h,
  intros p q,
  apply h,
  split,
  exact p,
  exact q

end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros h PandQ,
  cases PandQ with p q,
  have qr : Q→R := h p,
  have r : R := qr q,
  exact r,

end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  exact pq.left,

end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  exact pq.right,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,

  intro pp,
  exact pp.left,

  intro p,
  split,
  exact p,
  exact p,

end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  
  intro pp,
  cases pp with p p,
  exact p,
  exact p,

  intro p,
  left,
  exact p,

end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
