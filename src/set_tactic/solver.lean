import .extensionality
import .boolean_algebra_tactic
import .finset_tactic
import tactic
import tactic.interactive
import .set_tactic


universe u

/-meta def simpl_tactic : tactic unit :=
`[simp only [simpl_sdiff, simpl_eq, ext_le, ext_bot, ext_top, ext_meet, ext_join, ext_compl] at *; tauto!]-/


-- TODO: Lots of things are boolean algebras.  We should have a way to configure
-- which boolean algebras we want to solve, actually.
--
-- Functions into boolean algebras are usually not useful, so we ignore them by default.
-- Moreover, hypotheses are either Prop or functions which indirectly produce a Prop,
-- so we really should probably ignore function types with Prop in them.
meta def get_boolalg_typ (consider_function_types := ff) (e : expr) : tactic (list expr) :=
  ((do
    `(%%boolalg_typ) <- tactic.infer_type e,
    match boolalg_typ with 
    -- finset T gets returned directly 
    | `(finset %%set_typ) := do return [boolalg_typ]
    -- set T gets returned directly
    | `(set %%set_typ) := do return [boolalg_typ]
    -- work needs to be done if we're not working with sets/finsets,
    -- but with a type with a [boolean_algebra T] instance on it.
    | _ := (do 
        boolalg_hyp <- tactic.to_expr ``(infer_instance : boolean_algebra %%boolalg_typ),
        match boolalg_typ with 
        -- Function types are usually not useful
        | `(_ -> _) := if consider_function_types then return [boolalg_typ] else return []
        -- Prop is not useful
        | `(Prop) := return []
        -- Other types, we can (probably) return
        | _ := return [boolalg_typ]
        end)
    end)
  <|>
    return [])

meta def boolean_algebra_types_in_expr (consider_function_types := ff) : expr → tactic (list expr)
| e :=
  do 
    e_inner <- (match e with
      -- This mostly handles basic expressions 
      | expr.local_const unique pretty _ _ := get_boolalg_typ consider_function_types e
      -- applications
      | expr.app e1 e2 := 
        do l1 <- boolean_algebra_types_in_expr e1, 
          l2 <- boolean_algebra_types_in_expr e2,
          return (l1 ++ l2)
      -- abstracts
      | expr.lam _ _ argtyp body :=
        do l1 <- boolean_algebra_types_in_expr argtyp, 
          l2 <- boolean_algebra_types_in_expr body,
          return (l1 ++ l2)
      | expr.pi _ _ argtyp body :=
        do l1 <- boolean_algebra_types_in_expr argtyp, 
          l2 <- boolean_algebra_types_in_expr body,
          return (l1 ++ l2)
      | expr.elet _ argtyp argval body := 
        do l1 <- boolean_algebra_types_in_expr argtyp, 
          l2 <- boolean_algebra_types_in_expr argval,
          l3 <- boolean_algebra_types_in_expr body,
          return (l1 ++ l2 ++ l3)
      | _ := return []
      end),
    e_outer <- get_boolalg_typ consider_function_types e,
    return (e_inner ++ e_outer)

def unique_list {T: Type*} [decidable_eq T]: list T -> list T 
| [] := []
| (x :: xs) := let tl := unique_list xs in
                if list.mem x tl then tl else x :: tl

meta def infer_base_simp_lemmas (type : expr) : (tactic (list pexpr)) := do
  name <- tactic.get_unused_name `_instrw,
  instance_type <- tactic.to_expr ``(boolalg_ext_lemmas %%type _),
  expr <- tactic.to_expr ``(by apply_instance : %%instance_type),
  new_hyp <- tactic.assertv name instance_type expr,
  return [``((%%new_hyp).simpl_eq),
          ``((%%new_hyp).simpl_lt),
          ``((%%new_hyp).ext_le),
          ``((%%new_hyp).ext_bot),
          ``((%%new_hyp).ext_sdiff),
          ``((%%new_hyp).ext_meet),
          ``((%%new_hyp).ext_join)]

meta def infer_top_simp_lemmas (type : expr) : (tactic (list pexpr)) := (do
  name <- tactic.get_unused_name `_instrw,
  instance_type <- tactic.to_expr ``(boolalg_ext_lemmas_top %%type _),
  expr <- tactic.to_expr ``(by apply_instance : %%instance_type),
  new_hyp <- tactic.assertv name instance_type expr,
  return [``((%%new_hyp).ext_top)]) <|> return []

meta def infer_compl_simp_lemmas (type : expr) : (tactic (list pexpr)) := (do
  name <- tactic.get_unused_name `_instrw,
  instance_type <- tactic.to_expr ``(boolalg_ext_lemmas_compl %%type _),
  expr <- tactic.to_expr ``(by apply_instance : %%instance_type),
  new_hyp <- tactic.assertv name instance_type expr,
  return [``((%%new_hyp).ext_compl)]) <|> return []

meta def rewrite_for_type (type : expr) : (tactic unit) := do
  simp_lemmas <- infer_base_simp_lemmas type,
  compl_lemmas <- infer_compl_simp_lemmas type,
  top_lemmas <- infer_top_simp_lemmas type,
  tactic.try (tactic.interactive.simp none tt
              ((simp_lemmas ++ compl_lemmas ++ top_lemmas).map tactic.simp_arg_type.expr)
                  list.nil interactive.loc.wildcard),
  tactic.skip

meta def gather_types (consider_function_types := ff) : (tactic (list expr)) := do
  goal <- tactic.target,
  hyps <- tactic.local_context,
  types <- (do 
            types_in_expr <- (goal :: hyps).mmap (boolean_algebra_types_in_expr consider_function_types),
            return (unique_list (list.foldr list.append [] types_in_expr))),
  --tactic.trace "Boolean algebra types:",
  --tactic.trace types,
  return types


meta def set_ext (consider_function_types := ff) : (tactic unit) := do
  tactic.try `[simp only [ne, ge, gt, superset, ssuperset] at *],
  tactic.try cleanup.finset_cleanup,
  tactic.try cleanup.set_cleanup,
  types <- gather_types consider_function_types,
  types.mmap rewrite_for_type,
  tactic.skip 


meta def specialize_all (ename : expr) : (tactic unit) := do
  context <- tactic.local_context,
  context.mmap (fun hyp, tactic.try $ do
    pf <- tactic.to_expr ``(%%hyp %%ename),
    tactic.note `H none pf,
    tactic.skip),
  tactic.skip

meta def introduce_and_specialize : (tactic unit) := do 
  target <- tactic.target,
  match target with
  | expr.lam nm _ argtyp body := do
    let basename := (if (nm.to_string = "ᾰ") then `H else nm) in do
    fname <- tactic.get_unused_name basename,
    exp <- tactic.intro fname,
    specialize_all exp
  | expr.pi nm _ argtyp body := do
    let basename := (if (nm.to_string = "ᾰ") then `H else nm) in do
    fname <- tactic.get_unused_name basename,
    ename <- tactic.intro fname,
    specialize_all ename
  | _ := tactic.fail "goal not an abstraction"
  end

meta def clear_existential_hyp (hyp : expr) : (tactic (option expr)) := do
  htyp <- tactic.infer_type hyp,
  match htyp with
  | `(@Exists _ _) := do 
      [(_, [witness, _])] <- tactic.cases hyp,
      return (some witness)
  | _ := return none
  end

meta def forall_hypotheses (f : expr -> tactic unit) : (tactic unit) := do
  context <- tactic.local_context,
  result <- context.mmap (fun hyp, (f hyp >> return tt) <|> return ff),
  if (result.filter (fun (x : bool), x)).empty then 
    tactic.fail "could not apply function to any hypothesis" 
  else tactic.skip

meta def clear_existentials_hyp_and_specialize : (tactic unit) := do
  forall_hypotheses (fun hyp, 
    do some witness <- clear_existential_hyp hyp, specialize_all witness
  ) <|> tactic.fail "no existentials present"

meta def clear_existential_goal : (tactic unit) := do
  target <- tactic.target,
  match target with
  | `(@Exists %%typ _) := do
    mvar <- tactic.mk_meta_var typ,
    tactic.existsi mvar,
    tactic.skip
  | _ := tactic.fail "goal is not existential"
  end

meta def split_hypothesis (hyp : expr) : (tactic unit) := do
  htyp <- tactic.infer_type hyp,
  match htyp with
  | `(_ /\ _) := tactic.cases hyp >> tactic.skip
  | _ := tactic.fail "hypothesis is not conjunction"
  end

meta def split_all_hypothesis : (tactic unit) := do
  forall_hypotheses split_hypothesis <|> tactic.fail "no conjunctions in hypothesis"

meta def split_goal : (tactic unit) := do
  target <- tactic.target,
  match target with
  | `(_ /\ _) := tactic.split >> tactic.skip
  | _ := tactic.fail "not a conjunction"
  end
 
meta def finisher_step : (tactic unit) := do
  -- push negatives everywhere
  tactic.try `[push_neg at *],
  tactic.try `[push_neg],
  -- try introducing a name and specializing
  introduce_and_specialize 
  <|>
  -- if that fails, eliminate existentials in the goal by filling them in
  -- with a metavariable.
  -- maybe: fail instead?  We can't automatically determine what should go in.
  clear_existential_goal
  <|>
  -- if that fails, attempt to clear existentials
  clear_existentials_hyp_and_specialize
  <|>
  -- if that fails, split all hypothesis that are conjunctions
  split_all_hypothesis
  <|>
  -- if that fails, split the goal if it is a conjunction
  split_goal
  <|>
  -- if that fails, run tauto.
  -- TODO: fill in metavariables somehow introduced by existentials????
  -- this can be hard.
  `[tauto! {closer := tactic.tidy}]

meta def set_solver_finisher : (tactic unit) := do
  tactic.repeat finisher_step,
  -- we may have a list of goals -- we need to finish all of them
  -- in order to succeed.
  tactic.all_goals $ (
    tactic.target >>= (fun (target : expr),
    match target with
    -- if there is a disjunction in the goal, try either side
    | `(_ \/ _) := ((tactic.left >> set_solver_finisher) <|> (tactic.right >> set_solver_finisher)) >> tactic.skip
    -- if there is a disjucntion in the hypothesis, split it and make sure both sides work.
    | _ := (do 
      mvar1 <- tactic.mk_mvar,
      mvar2 <- tactic.mk_mvar,
      disj <- tactic.find_assumption `(%%mvar1 \/ %%mvar2),
      -- if we can't find such as disjunction, then we fail as the finisher could not work.
      tactic.cases disj [],
      tactic.all_goals set_solver_finisher,
      tactic.skip)
    end)),
  tactic.skip

meta def set_solver (consider_function_types := ff) : (tactic unit) := do
  set_ext consider_function_types,
  set_solver_finisher

example (α : Type*) [boolean_algebra α] (X Y Z P Q W : α) :
  (X ⊔ (Y ⊔ Z)) ⊔ ((W ⊓ P ⊓ Q)ᶜ ⊔ (P ⊔ W ⊔ Q)) = ⊤ :=
begin
  set_solver,
end

example (T : Type*) [fintype T] [decidable_eq T] (X Y Z P Q W : finset T)  :
  (X ⊔ (Y ⊔ Z)) ⊔ ((W ⊓ P ⊓ Q)ᶜ ⊔ (P ⊔ W ⊔ Q)) = ⊤ :=
begin
  set_solver,
end

-- note the lack of fintype T here
example (T : Type*) [decidable_eq T] (X Y Z P Q W : finset T)  :
  (X ∪ Y) ≥ X :=
begin
  set_solver,
end

example (T : Type*) [decidable_eq T] (x z : T) (Y : set T) :
  x ∈ ({z} : set T) → x = z :=
begin
  set_solver,
end

example (α : Type*) [boolean_algebra α]  (A B C D E F G : α) :
  A ≤ B →
  B ≤ C →
  C ≤ D ⊓ E →
  D ≤ Fᶜ →
  (A ⊓ F = ⊥) :=
begin
  set_ext,
  tactic.timetac "fast" $ (`[repeat {finisher_step}]),
end

example (α : Type*) [boolean_algebra α]  (A B C D E F G : α) :
  A ≤ B →
  B ≤ C →
  C ≤ D ⊓ E →
  D ≤ Fᶜ →
  (A ⊓ F = ⊥) :=
begin
  tactic.timetac "slow" $ set_solver,
end
 
example (α : Type*) (C E : set α) (hCE : C ⊓ E = ∅) :
  C ⊔ (E ⊔ C)ᶜ = Eᶜ := 
by {set_solver, }

example (α : Type*) (C E : set α) (h : C ⊓ E = ⊥) : 
  C ⊓ (C ⊔ E)ᶜ = ∅ := 
by {set_solver, } 

example (X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : set nat) :
  (X₀ ⊔ X₁ ⊔ (X₂ ⊓ X₃) ⊔ X₄ ⊔ X₅ ⊔ (X₆ ⊓ X₇ ⊓ X₈) ⊔ X₉)ᶜ
    ≤ (X₉ᶜ ⊓ ((X₆ᶜ ⊔ ⊥) ⊔ X₈ᶜ ⊔ X₇ᶜᶜᶜ) ⊓ X₅ᶜ ⊓ (X₀ᶜ \ X₁) ⊓ (X₃ᶜ ⊔ X₂ᶜ) ⊓ X₄ᶜ) :=
begin
  tactic.timetac "big_ext" $ set_ext,
  tactic.timetac "big_finish" $ set_solver_finisher
end

/-
example (X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : α) :
  (X₀ ⊔ X₁ ⊔ (X₂ ⊓ X₃) ⊔ X₄ ⊔ X₅ ⊔ (X₆ ⊓ X₇ ⊓ X₈) ⊔ X₉)ᶜ
    ≤ (X₉ᶜ ⊓ ((X₆ᶜ ⊔ ⊥) ⊔ X₈ᶜ ⊔ X₇ᶜᶜᶜ) ⊓ X₅ᶜ ⊓ (X₀ᶜ \ X₁) ⊓ (X₃ᶜ ⊔ X₂ᶜ) ⊓ X₄ᶜ) :=
by tactic.timetac "big" $ boolean_algebra_tactic

example (A B C D E F G : α) :
  A ≤ B →
  B ≤ C →
  C ≤ D ⊓ E →
  A ≤ E :=
begin
  simp only [rw_sdiff, rw_eq, rw_le, rw_bot, rw_top, rw_sup, rw_inf, rw_compl] at *,
  intros H1 H2 H3 u H4,
  specialize (H1 u),
  specialize (H2 u),
  specialize (H3 u),
  tauto!
end

example (A B C D E F G : α) :
  A ≤ B →
  B ≤ C →
  C ≤ D ⊓ E →
  D ≤ Fᶜ →
  (A ⊓ F = ⊥) :=
begin
  simp only [rw_sdiff, rw_eq, rw_le, rw_bot, rw_top, rw_sup, rw_inf, rw_compl] at *,
  intros H1 H2 H3 H4,
  split;
  intro u, specialize (H1 u), specialize (H2 u), specialize (H3 u), specialize (H4 u), tauto!,
  tauto!,
end
-/
