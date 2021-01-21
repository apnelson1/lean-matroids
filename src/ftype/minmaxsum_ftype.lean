-- Experimental/broken - nothing relies on this. 

import .basic .induction .single 
----------------------------------------------------------------
open_locale classical 
noncomputable theory 

namespace ftype 
-- The operations needed on the ftype A.
section minmax

variables {α : ftype}[nonempty α]{β : Type}[linear_order β]

--instance i : has_coe_to_sort (set α) := 
--{S := ftype, coe := λ X, { E := X, fin := by {letI := α.fin, apply_instance }}}


instance duh {γ : ftype} : fintype γ := by {letI := γ.fin, apply_instance} 

instance i {γ : Type}[fintype γ]: has_coe_to_sort γ := 
{ S := ftype , coe := λ X, { E := X, fin := _ } }
-- Proving this stuff probably needs fintype etc for ftype. 


/-- finds the argmin of f over all sets X satisfying P -/
lemma exists_arg_max_over_subtype (P : set α)[nonempty P](f : P → β): 
  ∃ X, ∀ Y, f Y ≤ f X := 
begin
  letI := fintype_of α,
  from fintype.exists_max f,
end

/-- finds the argmin of f over all sets X satisfying P -/
lemma exists_arg_min_over_subtype (P : set α)[nonempty P] (f : P → β): 
  ∃ X, ∀ Y, f X ≤ f Y := 
let f' : _ → (order_dual β) := f in exists_arg_max_over_subtype P f'

/-- maximum value of f over subsets of U satisfying P -/
def arg_max_over (P : set α)[nonempty P](f : α → β) : α := 
  (classical.some (exists_arg_max_over_subtype P (λ x, f x.val))).val 

/-- subset of U attaining maximum value of f subject to satisfying P -/
def max_val_over (P : set α)[nonempty P](f : α → β) : β := 
  f (arg_max_over P f)

lemma max_over_is_ub (P : set α)[nonempty P](f : α → β):
  ∀ X, P X → f X ≤ max_val_over P f :=
λ X hX, classical.some_spec (exists_arg_max_over_subtype P (λ X, f X.val)) ⟨X, hX⟩
  
lemma arg_max_over_attains (P : set α)[nonempty P](f : α → β):
  P (arg_max_over P f) ∧ f (arg_max_over P f) = max_val_over P f := 
let X' := (classical.some (exists_arg_max_over_subtype P (λ X, f X.val))) in 
⟨X'.property, rfl⟩  

lemma max_over_spec (P : set α)[nonempty P](f : α → β):
  ∃ X, P X ∧ (f X = max_val_over P f) ∧ (∀ Y, P Y → f Y ≤ f X)  := 
let prev := arg_max_over_attains P f in 
⟨arg_max_over P f,⟨prev.1,prev.2,max_over_is_ub P f⟩⟩  

/-- minimum value of f over subsets of U satisfying P -/
def arg_min_over (P : set α)[nonempty P](f : α → β) : α :=  
  (classical.some (exists_arg_min_over_subtype P (λ X, f X.val))).val 

/-- subset of U attaining minimum value of f subject to satisfying P -/
def min_val_over (P : set α)[nonempty P](f : α → β) : β := 
  f (arg_min_over P f)


lemma min_over_is_lb (P : set α)[nonempty P](f : α → β):
  ∀ X, P X → min_val_over P f ≤ f X := 
λ X hX, classical.some_spec (exists_arg_min_over_subtype P (λ X, f X.val)) ⟨X, hX⟩


lemma arg_min_over_attains (P : set α)[nonempty P](f : α → β):
  P (arg_min_over P f) ∧ f (arg_min_over P f) = min_val_over P f := 
let X' := (classical.some (exists_arg_min_over_subtype P (λ X, f X.val))) in 
⟨X'.property, rfl⟩    

lemma min_over_spec (P : set α)[nonempty P](f : α → β):
  ∃ X, P X ∧ (f X = min_val_over P f) ∧ (∀ Y, P Y → f X ≤ f Y)   := 
let prev := arg_min_over_attains P f in 
⟨arg_min_over P f,⟨prev.1,prev.2,min_over_is_lb P f⟩⟩ 
---- 

/-- maximum value of f over subsets of U -/
def max_val (f : α → β) : β := max_val_over univ f

/-- subset of U attaining maximum value of f -/
def arg_max (f : α → β) : α := arg_max_over univ f

/-- minimum value of f over subsets of U -/
def min_val (f : α → β) : β := min_val_over univ f

/-- subset of U attaining minimum value of f-/
def arg_min (f : α → β) : α := arg_min_over univ f

lemma max_is_ub (f : α → β): 
  ∀ X, f X ≤ max_val f :=
λ X, by {apply max_over_is_ub, trivial}

lemma arg_max_attains (f : α → β): 
  f (arg_max f) = max_val f :=
(arg_max_over_attains _ _).2

lemma min_is_lb (f : α → β) :
  ∀ X, min_val f ≤ f X := 
λ X, by {apply min_over_is_lb, trivial} 

lemma arg_min_attains (f : α → β) : 
  f (arg_min f) = min_val f := 
(arg_min_over_attains _ _).2

lemma min_spec (f : α → β):
  ∃ X, (∀ Y, f X ≤ f Y) ∧ (f X = min_val f) := 
⟨arg_min f, ⟨min_is_lb f, arg_min_attains f⟩ ⟩  

lemma max_spec (f : α → β):
  ∃ X, (∀ Y, f Y ≤ f X) ∧ (f X = max_val f) := 
⟨arg_max f, ⟨max_is_ub f, arg_max_attains f⟩ ⟩


-- size 

/-- largest set satisfying P -/
def arg_max_size_over (P : set (set α))[nonempty P] : set α := 
  arg_max_over P size  

/-- size of largest set satisfying P -/
def max_size_over (P : α → Prop)(hP : set.nonempty P): ℤ := 
  size (arg_max_size_over P)

lemma max_size_over_is_ub (P : α → Prop)(hP : set.nonempty P):
  ∀ X, P X → size X ≤ max_size_over P:=
max_over_is_ub P size 
  
lemma arg_max_size_over_attains (P : α → Prop)(hP : set.nonempty P):
  P (arg_max_size_over P) ∧ size (arg_max_size_over P) = max_size_over P := 
  arg_max_over_attains P size 

lemma max_size_over_spec (P : α → Prop)(hP : set.nonempty P):
  ∃ X, P X ∧ (size X = max_size_over P) ∧ (∀ Y, P Y → size Y ≤ size X)  := 
  max_over_spec P size 


/-- smallest set satisfying P -/
def arg_min_size_over (P : α → Prop)(hP : set.nonempty P) : α := 
  arg_min_over P size  

/-- size of smallest set satisfying P -/
def min_size_over (P : α → Prop)(hP : set.nonempty P): ℤ := 
  size (arg_min_size_over P)

lemma min_size_over_is_lb (P : α → Prop)(hP : set.nonempty P):
  ∀ X, P X → min_size_over P ≤ size X :=
min_over_is_lb P size 
  
lemma arg_min_size_over_attains (P : α → Prop)(hP : set.nonempty P):
  P (arg_min_size_over P) ∧ size (arg_min_size_over P) = min_size_over P := 
  arg_min_over_attains P size 

lemma min_size_over_spec (P : α → Prop)(hP : set.nonempty P):
  ∃ X, P X ∧ (size X = min_size_over P) ∧ (∀ Y, P Y → size X ≤ size Y)  := 
  min_over_spec P size 

--- Monotonicity 

lemma max_over_subset_le_max (P Q : α → Prop)(hP : set.nonempty P)(f : α → β)(hPQ : set.subset P Q): 
   max_val_over P f ≤ max_val_over Q (set.nonempty.mono hPQ hP) f := 
begin
  rcases max_over_spec P f with ⟨XP, hXP⟩, 
  rcases max_over_spec Q (set.nonempty.mono hPQ hP) f with ⟨XQ, hXQ⟩,
  rw [←hXP.2.1, ←hXQ.2.1], 
  from hXQ.2.2  _ (hPQ hXP.1),
end

lemma min_le_min_over_subset (P Q : α → Prop)(hP : set.nonempty P)(f : α → β)(hPQ : set.subset P Q):
  min_val_over Q (set.nonempty.mono hPQ hP) f ≤ min_val_over P f := 
begin
  rcases min_over_spec P f with ⟨XP, hXP⟩, 
  rcases min_over_spec Q (set.nonempty.mono hPQ hP) f with ⟨XQ, hXQ⟩,
  rw [←hXP.2.1, ←hXQ.2.1], 
  from hXQ.2.2  _ (hPQ hXP.1),
end

lemma max_over_le_max_over_of_mono (P : α → Prop)(hP : set.nonempty P)(f f' : α → α)(hff' : ∀ X, f X ≤ f' X):
  max_val_over P f ≤ max_val_over P f' := 
begin
  rcases max_over_spec P f with ⟨X,hX⟩, 
  rcases max_over_spec P f' with ⟨X', hX'⟩, 
  rw [←hX.2.1, ←hX'.2.1], 
  from le_trans (hff' X) (hX'.2.2 _ hX.1), 
end

lemma min_over_le_min_over_of_mono (P : α → Prop)(hP : set.nonempty P)(f f' : α → α)(hff' : ∀ X, f X ≤ f' X):
  min_val_over P f ≤ min_val_over P f' := 
begin
  rcases min_over_spec P f with ⟨X,hX⟩, 
  rcases min_over_spec P f' with ⟨X', hX'⟩, 
  rw [←hX.2.1, ←hX'.2.1], 
  from le_trans (hX.2.2 X' hX'.1) (hff' _),
end





end minmax


end ftype 
