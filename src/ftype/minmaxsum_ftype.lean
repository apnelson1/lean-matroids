import .basic .induction .single 
----------------------------------------------------------------
open_locale classical 
noncomputable theory 


namespace ftype 
-- The operations needed on the ftype A.
section minmax

variables {α : ftype}{β : Type}[nonempty α][linear_order β]

-- Proving this stuff probably needs fintype etc for ftype. 


/-- finds the argmin of f over all sets X satisfying P -/
lemma exists_arg_max_over_subtype (P : set U → Prop)(hP : set.nonempty P) (f : { X : set U // P X } → α): 
  ∃ X, ∀ Y, f Y ≤ f X := 
begin
  letI := fintype_of U,
  haveI : nonempty { X : set U // P X } := ⟨classical.subtype_of_exists hP⟩, 
  from fintype.exists_max f, 
end

/-- finds the argmin of f over all sets X satisfying P -/
lemma exists_arg_min_over_subtype (P : set U → Prop)(hP : set.nonempty P) (f : { X : set U // P X } → α): 
  ∃ X, ∀ Y, f X ≤ f Y := 
let f' : _ → (order_dual α) := f in exists_arg_max_over_subtype P hP f'


/-- maximum value of f over subsets of U satisfying P -/
def arg_max_over (P : set U → Prop)(hP : set.nonempty P)(f : set U → α) : set U := 
  (classical.some (exists_arg_max_over_subtype P hP (λ X, f X.val))).val 

/-- subset of U attaining maximum value of f subject to satisfying P -/
def max_val_over (P : set U → Prop)(hP : set.nonempty P)(f : set U → α) : α := 
  f (arg_max_over P hP f)

lemma max_over_is_ub (P : set U → Prop)(hP : set.nonempty P)(f : set U → α):
  ∀ X, P X → f X ≤ max_val_over P hP f :=
λ X hX, classical.some_spec (exists_arg_max_over_subtype P hP (λ X, f X.val)) ⟨X, hX⟩
  
lemma arg_max_over_attains (P : set U → Prop)(hP : set.nonempty P)(f : set U → α):
  P (arg_max_over P hP f) ∧ f (arg_max_over P hP f) = max_val_over P hP f := 
let X' := (classical.some (exists_arg_max_over_subtype P hP (λ X, f X.val))) in 
⟨X'.property, rfl⟩  

lemma max_over_spec (P : set U → Prop)(hP : set.nonempty P)(f : set U → α):
  ∃ X, P X ∧ (f X = max_val_over P hP f) ∧ (∀ Y, P Y → f Y ≤ f X)  := 
let prev := arg_max_over_attains P hP f in 
⟨arg_max_over P hP f,⟨prev.1,prev.2,max_over_is_ub P hP f⟩⟩  

/-- minimum value of f over subsets of U satisfying P -/
def arg_min_over (P : set U → Prop)(hP : set.nonempty P)(f : set U → α) : set U :=  
  (classical.some (exists_arg_min_over_subtype P hP (λ X, f X.val))).val 

/-- subset of U attaining minimum value of f subject to satisfying P -/
def min_val_over (P : set U → Prop)(hP : set.nonempty P)(f : set U → α) : α := 
  f (arg_min_over P hP f)



lemma min_over_is_lb (P : set U → Prop)(hP : set.nonempty P)(f : set U → α):
  ∀ X, P X → min_val_over P hP f ≤ f X := 
λ X hX, classical.some_spec (exists_arg_min_over_subtype P hP (λ X, f X.val)) ⟨X, hX⟩


lemma arg_min_over_attains (P : set U → Prop)(hP : set.nonempty P)(f : set U → α):
  P (arg_min_over P hP f) ∧ f (arg_min_over P hP f) = min_val_over P hP f := 
let X' := (classical.some (exists_arg_min_over_subtype P hP (λ X, f X.val))) in 
⟨X'.property, rfl⟩    

lemma min_over_spec (P : set U → Prop)(hP : set.nonempty P)(f : set U → α):
  ∃ X, P X ∧ (f X = min_val_over P hP f) ∧ (∀ Y, P Y → f X ≤ f Y)   := 
let prev := arg_min_over_attains P hP f in 
⟨arg_min_over P hP f,⟨prev.1,prev.2,min_over_is_lb P hP f⟩⟩ 
---- 

/-- maximum value of f over subsets of U -/
def max_val (f : set U → α) : α := max_val_over (λ X, true) ⟨∅, trivial⟩ f

/-- subset of U attaining maximum value of f -/
def arg_max (f : set U → α) : set U := arg_max_over (λ X, true) ⟨∅, trivial⟩ f

/-- minimum value of f over subsets of U -/
def min_val (f : set U → α) : α := min_val_over (λ X, true) ⟨∅, trivial⟩ f

/-- subset of U attaining minimum value of f-/
def arg_min (f : set U → α) : set U := arg_min_over (λ X, true) ⟨∅, trivial⟩ f

lemma max_is_ub (f : set U → α): 
  ∀ X, f X ≤ max_val f :=
λ X, by {apply max_over_is_ub, trivial} 

lemma arg_max_attains (f : set U → α): 
  f (arg_max f) = max_val f :=
(arg_max_over_attains _ _ _).2

lemma min_is_lb (f : set U → α) :
  ∀ X, min_val f ≤ f X := 
λ X, by {apply min_over_is_lb, trivial} 

lemma arg_min_attains (f : set U → α) : 
  f (arg_min f) = min_val f := 
(arg_min_over_attains _ _ _).2

lemma min_spec (f : set U → α):
  ∃ X, (∀ Y, f X ≤ f Y) ∧ (f X = min_val f) := 
⟨arg_min f, ⟨min_is_lb f, arg_min_attains f⟩ ⟩  

lemma max_spec (f : set U → α):
  ∃ X, (∀ Y, f Y ≤ f X) ∧ (f X = max_val f) := 
⟨arg_max f, ⟨max_is_ub f, arg_max_attains f⟩ ⟩


-- size 

/-- largest set satisfying P -/
def arg_max_size_over (P : set U → Prop)(hP : set.nonempty P) : set U := 
  arg_max_over P hP size  

/-- size of largest set satisfying P -/
def max_size_over (P : set U → Prop)(hP : set.nonempty P): ℤ := 
  size (arg_max_size_over P hP)

lemma max_size_over_is_ub (P : set U → Prop)(hP : set.nonempty P):
  ∀ X, P X → size X ≤ max_size_over P hP:=
max_over_is_ub P hP size 
  
lemma arg_max_size_over_attains (P : set U → Prop)(hP : set.nonempty P):
  P (arg_max_size_over P hP) ∧ size (arg_max_size_over P hP) = max_size_over P hP := 
  arg_max_over_attains P hP size 

lemma max_size_over_spec (P : set U → Prop)(hP : set.nonempty P):
  ∃ X, P X ∧ (size X = max_size_over P hP) ∧ (∀ Y, P Y → size Y ≤ size X)  := 
  max_over_spec P hP size 


/-- smallest set satisfying P -/
def arg_min_size_over (P : set U → Prop)(hP : set.nonempty P) : set U := 
  arg_min_over P hP size  

/-- size of smallest set satisfying P -/
def min_size_over (P : set U → Prop)(hP : set.nonempty P): ℤ := 
  size (arg_min_size_over P hP)

lemma min_size_over_is_lb (P : set U → Prop)(hP : set.nonempty P):
  ∀ X, P X → min_size_over P hP ≤ size X :=
min_over_is_lb P hP size 
  
lemma arg_min_size_over_attains (P : set U → Prop)(hP : set.nonempty P):
  P (arg_min_size_over P hP) ∧ size (arg_min_size_over P hP) = min_size_over P hP := 
  arg_min_over_attains P hP size 

lemma min_size_over_spec (P : set U → Prop)(hP : set.nonempty P):
  ∃ X, P X ∧ (size X = min_size_over P hP) ∧ (∀ Y, P Y → size X ≤ size Y)  := 
  min_over_spec P hP size 

--- Monotonicity 

lemma max_over_subset_le_max (P Q : set U → Prop)(hP : set.nonempty P)(f : set U → α)(hPQ : set.subset P Q): 
   max_val_over P hP f ≤ max_val_over Q (set.nonempty.mono hPQ hP) f := 
begin
  rcases max_over_spec P hP f with ⟨XP, hXP⟩, 
  rcases max_over_spec Q (set.nonempty.mono hPQ hP) f with ⟨XQ, hXQ⟩,
  rw [←hXP.2.1, ←hXQ.2.1], 
  from hXQ.2.2  _ (hPQ hXP.1),
end

lemma min_le_min_over_subset (P Q : set U → Prop)(hP : set.nonempty P)(f : set U → α)(hPQ : set.subset P Q):
  min_val_over Q (set.nonempty.mono hPQ hP) f ≤ min_val_over P hP f := 
begin
  rcases min_over_spec P hP f with ⟨XP, hXP⟩, 
  rcases min_over_spec Q (set.nonempty.mono hPQ hP) f with ⟨XQ, hXQ⟩,
  rw [←hXP.2.1, ←hXQ.2.1], 
  from hXQ.2.2  _ (hPQ hXP.1),
end

lemma max_over_le_max_over_of_mono (P : set U → Prop)(hP : set.nonempty P)(f f' : set U → α)(hff' : ∀ X, f X ≤ f' X):
  max_val_over P hP f ≤ max_val_over P hP f' := 
begin
  rcases max_over_spec P hP f with ⟨X,hX⟩, 
  rcases max_over_spec P hP f' with ⟨X', hX'⟩, 
  rw [←hX.2.1, ←hX'.2.1], 
  from le_trans (hff' X) (hX'.2.2 _ hX.1), 
end

lemma min_over_le_min_over_of_mono (P : set U → Prop)(hP : set.nonempty P)(f f' : set U → α)(hff' : ∀ X, f X ≤ f' X):
  min_val_over P hP f ≤ min_val_over P hP f' := 
begin
  rcases min_over_spec P hP f with ⟨X,hX⟩, 
  rcases min_over_spec P hP f' with ⟨X', hX'⟩, 
  rw [←hX.2.1, ←hX'.2.1], 
  from le_trans (hX.2.2 X' hX'.1) (hff' _),
end





end minmax


end ftype 
