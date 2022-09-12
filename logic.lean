
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
  by_contradiction notp,
  contradiction,
  
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  exact doubleneg_elim P,
  exact doubleneg_intro P,
  
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

theorem impl_as_contrapositive_converse :
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

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro h,
  by_contradiction j,
  
  apply j,
  left,
  intro q,

  apply j,
  right,
  intro p,

  apply h,
  split,
  
  exact p,
  exact q,


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
  intro notx,
  intro x,
  intro px,

  apply notx,
  existsi x,
  exact px,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro fallxnotp,
  intro notxpx,
  
  cases notxpx with x px,
  have a := fallxnotp x,
  contradiction,

end

theorem demorgan_forall : --feitiço
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro notpx,
  by_contradiction NEnpx,
  
  apply notpx,
  intro x,

  by_contradiction notpx,
  apply NEnpx,
  existsi x,
  exact notpx,

end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro enpx,
  cases enpx with x notpx,
  intro allpx,
  have a := allpx x,
  contradiction,

end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  exact demorgan_forall U P,
  exact demorgan_forall_converse U P,

end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  exact demorgan_exists U P,
  exact demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro expx,
  intro allnotpx,

  cases expx with x px,
  have notpx := allnotpx x,
  contradiction,

end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro allpx,
  intro existnotpx,

  cases existnotpx with x notpx,
  have px := allpx x,
  contradiction,

end

theorem forall_as_neg_exists_converse : -- feitiço
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro Nnpx,
  intro x,
  by_contradiction px,

  apply Nnpx,
  existsi x,
  exact px,
end

theorem exists_as_neg_forall_converse : --feitiço
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro notallnotpx,
  by_contradiction NEpx,

  apply notallnotpx,
  intro x,
  intro px,

  apply NEpx,
  existsi x,
  exact px,

end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  exact forall_as_neg_exists U P,
  exact forall_as_neg_exists_converse U P,
  
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  exact exists_as_neg_forall U P,
  exact exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro pxandqx,
  cases pxandqx with x pxandqx,
  cases pxandqx with px qx,

  split,
  existsi x,
  exact px,

  existsi x,
  exact qx,
  
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro pxorqx,
  cases pxorqx with x a,

  cases a with px qx,
  left,
  existsi x,
  exact px,

  right,
  existsi x,
  exact qx,

end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with l r,

  cases l with x px,
  
  existsi x,
  left,
  exact px,

  cases r with x qx,

  existsi x,
  right,
  exact qx,

end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,

  intro x,
  have props := h x,
  cases props with px qx,
  exact px,

  intro x,
  have props := h x,
  cases props with px qx,
  exact qx,

end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro h,
  cases h with l r,
  intro x,
  have px := l x,
  have qx := r x,
  
  split,
  exact px,
  exact qx,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro h,
  intro x,

  cases h with l r,
  
  have px := l x,
  left,
  exact px,

  have qx := r x,
  right,
  exact qx,

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
