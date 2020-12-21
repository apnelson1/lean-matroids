import set_tactic.freealg

open interactive
open lean.parser
open tactic
open tactic.interactive («let» «have» simp refl)
open freealg

------------------------- Conversion Tactic: [(finset α) or (set α) or boolean_lattice] to [boolean_ring] 

lemma finset.inter_is_inf (α : Type) [decidable_eq α] (X Y : finset α) : X ∩ Y = X ⊓ Y := rfl
lemma finset.union_is_sup (α : Type) [decidable_eq α] (X Y : finset α) : X ∪ Y = X ⊔ Y := rfl
lemma finset.empt_is_bot (α : Type) [decidable_eq α] : (finset.has_emptyc.emptyc : finset α) = ⊥ := rfl
lemma finset.subset_is_le (α : Type) [decidable_eq α] (X Y : finset α) : (X ⊆ Y) = (X ≤ Y) := rfl 
--lemma finset.univ_is_top (α : Type) [decidable_eq α] : (finset.order_top : finset α) = ⊤ := 

lemma set.union_is_sup (α : Type) (X Y : set α) : X ∪ Y = X ⊔ Y := rfl
lemma set.inter_is_inf (α : Type) (X Y : set α) : X ∩ Y = X ⊓ Y := rfl
lemma set.empt_is_bot (α : Type) : (set.has_emptyc.emptyc : set α) = ⊥ := rfl 
lemma set.univ_is_top (α : Type) : (set.univ : set α) = ⊤ := rfl 
lemma set.subset_is_le (α : Type) (X Y : set α) : (X ⊆ Y) = (X ≤ Y) := rfl 

meta def to_ring_eqn : tactic unit := do
`[try {simp only
    [finset.inter_is_inf, finset.union_is_sup, finset.empt_is_bot, finset.subset_is_le,
     set.union_is_sup, set.inter_is_inf, set.empt_is_bot, set.univ_is_top, set.subset_is_le,
     top_to_ring, bot_to_ring, symm_diff_to_ring, inf_to_ring, sup_to_ring, 
      diff_to_ring, compl_to_ring, le_to_ring] at *}]

------------------------------ Normalization Tactics (in a free boolean algebra) -------------------------
meta def ids_list : lean.parser (list name) := types.list_of ident
meta def meta_build_vector : list pexpr -> pexpr
| [] := ``(vector.nil)
| (v :: vs) := ``(vector.cons %%v %%(meta_build_vector vs))
meta def list_with_idx {T : Type} : (list T) → nat -> list (nat × T)
| [] n := []
| (v :: vs) n := (n, v) :: list_with_idx vs (n + 1)

meta def tactic.interactive.introduce_varmap_rewrite (vname : parse ident) (vars : parse ids_list) : tactic unit :=
  do
    names <- vars.mmap (fun name, get_local name),
    («let» vname ``(vector _ %%(vars.length)) $ meta_build_vector (names.map to_pexpr)),
    mmap 
      (λ (pair : (nat × expr)),
        let name := prod.snd pair in
        let idx := prod.fst pair in
        do 
          vname_expr <- get_local vname,
          hname <- get_unused_name `Hv,
          («have» hname ``(%%name = _) ``(on_var %%vname_expr %%idx (by norm_num))),
          hname_expr <- get_local hname,
          tactic.try (rewrite_target hname_expr),
          return ())
      (list_with_idx names 0),
    return ()

meta def find_matching_type (e : expr) : list expr → tactic expr
| []         := tactic.failed
| (H :: Hs)  := do t ← tactic.infer_type H,
                   (tactic.unify e t >> return H) <|> find_matching_type Hs
set_option pp.all false
meta def get_sets_in_expr : expr → tactic (list name) 
| e :=
  match e with
  -- This mostly handles basic expressions 
  | expr.local_const unique pretty _ _ :=
    do
      expr <- get_local pretty,
      ((do
        `(finset _) <- tactic.infer_type expr, 
        return [pretty])
      <|>
       (do
        `(set _) <- tactic.infer_type expr,
        return [pretty])
      <|>
       (do
        `(%%typ) <- tactic.infer_type expr,
        boolalg_expr_to_find <- to_expr ``(boolean_algebra %%typ),
        _ <- find_assumption boolalg_expr_to_find,
        return [pretty])
      <|>
        return [])
  | expr.app e1 e2 := 
    do l1 <- get_sets_in_expr e1, 
       l2 <- get_sets_in_expr e2,
       return (l1 ++ l2)
  | _ := do return []
  end

def keep_unique {T: Type}[decidable_eq T]: list T -> list T 
| [] := []
| (x :: xs) := let tl := keep_unique xs in
                if list.mem x tl then tl else x :: tl
#reduce keep_unique [1, 2, 3, 1, 1]

/- A bound variable with a de-Bruijn index. -/
-- | var _ := tactic.failed ()
/- A type universe: `Sort u` -/
-- | sort l := do return ()
/- A global constant. These include definitions, constants and inductive type stuff present
in the environment as well as hard-coded definitions. -/
-- | const name l := do return ()
/- [WARNING] Do not trust the types for `mvar` and `local_const`,
they are sometimes dummy values. Use `tactic.infer_type` instead. -/
/- An `mvar` is a 'hole' yet to be filled in by the elaborator or tactic state. -/
-- | mvar unique pretty type := do return ()
/- A local constant. For example, if our tactic state was `h : P ⊢ Q`, `h` would be a local constant. -/
-- | local_const unique pretty binder type := do return ()
/- Function application. -/
-- | app e1 e2 := do return ()
/- Lambda abstraction. eg ```(λ a : α, x)`` -/
-- | lam name binder type body := do return ()
/- Pi type constructor. eg ```(Π a : α, x)`` and ```(α → β)`` -/
-- | pi name binder type body := do return ()
/- An explicit let binding. -/
--| elet name type assignment body := do return ()
/- A macro, see the docstring for `macro_def`.
  The list of expressions are local constants and metavariables that the macro depends on.
  -/
-- | expr.macro macro_def body := do return () 

meta def dummy : tactic unit :=
  do tactic.trace "Hello World"

meta def tactic.interactive.simplify_sets (extra_sets : (parse (optional ids_list))): tactic unit :=
  do
    -- TODO: actually check the goal is of the form of some boolalg equation
    --       also -- do something about hypotheses...
    texpr <- target,
    list_of_sets <- get_sets_in_expr texpr,
    vname <- get_unused_name `V,
    tactic.interactive.introduce_varmap_rewrite vname
      (keep_unique $ list_of_sets ++ match extra_sets with | some l := l | none := [] end ),
    vname_expr <- get_local vname,
    to_ring_eqn,
    -- Some goals are already discharged by this point, so everything else
    -- goes in a try block.
    
    tactic.try (simp none tt ([``(freealg.on_one %%vname_expr),
                   ``(freealg.on_add %%vname_expr),
                   ``(freealg.on_mul %%vname_expr),
                   ``(freealg.on_zero %%vname_expr),
                   ``(freealg.on_var %%vname_expr)].map simp_arg_type.expr)
                    list.nil loc.wildcard),
    tactic.try (refl)
