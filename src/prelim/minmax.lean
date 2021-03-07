
import .size .induction .single 
----------------------------------------------------------------
open_locale classical 
noncomputable theory 


-- Lemmas applying for a general nonempty fintype 
-- TODO - lemmas about folding, so sum etc is also subsumed 

section general_fintype 

variables {α α' β β': Type}[nonempty (fintype α)][nonempty α][linear_order β][linear_order β']

--instance fin_α : fintype α := by {letI := classical.choice _inst_1, apply_instance, }

/- theorem set.finite.exists_maximal_wrt {α : Type u} {β : Type v} [partial_order β]
(f : α → β)(s : set α) (h : s.finite) :
s.nonempty → (∃ (a : α) (H : a ∈ s), ∀ (a' : α), a' ∈ s → f a ≤ f a' → f a = f a') -/


lemma exists_max (f : α → β): 
  ∃ x, ∀ y, f y ≤ f x := 
begin
  letI := classical.choice _inst_1, 
  unfreezingI {obtain ⟨a₀⟩ := _inst_2}, 
  obtain ⟨a, -, ha⟩ := 
    set.finite.exists_maximal_wrt f set.univ (set.finite.of_fintype _) ⟨a₀, set.mem_univ a₀⟩,
  refine ⟨a, λ x, _⟩,  
  rcases le_total (f x) (f a) with (h | h), exact h, 
  exact le_of_eq (ha x (set.mem_univ _) h).symm, 
end

lemma exists_min (f : α → β): 
  ∃ x, ∀ y, f x ≤ f y := 
let f' : _ → (order_dual β) := f in exists_max f'  

/-- maximum value of f -/
def max_val (f : α → β) : β := 
  f (classical.some (exists_max f))
  
/-- minimum value of f -/
def min_val (f : α → β) : β := 
  f (classical.some (exists_min f))

lemma max_spec (f : α → β) : 
  ∃ x, f x = max_val f ∧ ∀ y, f y ≤ f x :=
⟨classical.some (exists_max f), ⟨rfl, classical.some_spec (exists_max f) ⟩⟩

lemma min_spec (f : α → β) : 
  ∃ x, f x = min_val f ∧ ∀ y, f x ≤ f y :=
⟨classical.some (exists_min f), ⟨rfl, classical.some_spec (exists_min f) ⟩⟩

lemma max_is_ub (f : α → β)(x : α): 
  f x ≤ max_val f := 
by {cases max_spec f with y hy, rw ←hy.1, apply hy.2}

lemma min_is_lb (f : α → β)(x : α): 
  min_val f ≤ f x := 
by {cases min_spec f with y hy, rw ←hy.1, apply hy.2}

lemma max_of_le_is_le (f f' : α → β)(hff' : ∀ a, f a ≤ f' a):
  max_val f ≤ max_val f' := 
begin
  cases max_spec f with a ha, 
  cases max_spec f' with a' ha', 
  rw [←ha.1, ←ha'.1], 
  from le_trans (hff' _) (ha'.2 _), 
end

lemma min_of_le_is_le (f f' : α → β)(hff' : ∀ a, f a ≤ f' a):
  min_val f ≤ min_val f' := 
begin
  cases min_spec f with a ha, 
  cases min_spec f' with a' ha', 
  rw [←ha.1, ←ha'.1], 
  from le_trans (ha.2 _) (hff' a'), 
end

def surj_fin {φ : α → α'}(hφ : function.surjective φ) : 
  nonempty (fintype α') := 
by {letI := classical.choice _inst_1, exact ⟨fintype.of_surjective φ hφ⟩, } 


/-- taking a max over one type is equivalent to taking one over another, 
given a bijection between them -/
lemma max_reindex (φ : α → α')(hφ : function.surjective φ)(f : α' → β):
  max_val (f ∘ φ) = @max_val _ _ (surj_fin hφ) (nonempty.map φ _inst_2) _ f := 
begin
  rcases @max_spec _ _ (surj_fin hφ) (nonempty.map φ _inst_2) _ f 
    with ⟨x', ⟨hx'1, hx'2⟩⟩, 
  rcases max_spec (f ∘ φ) with ⟨x, ⟨hx1, hx2⟩ ⟩, 
  rw [←hx1, ←hx'1], 
  apply le_antisymm (hx'2 _), 
  cases hφ x' with z hz,
  rw ←hz, apply hx2, 
end

/-- taking a min over one type is equivalent to taking one over another, 
given a bijection between them -/
lemma min_reindex (φ : α → α')(hφ : function.surjective φ)(f : α' → β):
  min_val (f ∘ φ) = @min_val _ _ (surj_fin hφ) (nonempty.map φ _inst_2) _ f := 
begin
  rcases @min_spec _ _ (surj_fin hφ) (nonempty.map φ _inst_2) _ f 
    with ⟨x', ⟨hx'1, hx'2⟩⟩, 
  rcases min_spec (f ∘ φ) with ⟨x, ⟨hx1, hx2⟩ ⟩, 
  rw [←hx1, ←hx'1], 
  refine le_antisymm _ (hx'2 _), 
  cases hφ x' with z hz,
  rw ←hz, apply hx2, 
end

/-- max commutes with composing by a monotone function -/
lemma max_compose_mono (f : α → β)(g : β → β')(hg : monotone g):
  g (max_val f) = max_val (g ∘ f) := 
begin
  rcases max_spec f with ⟨X, hX₁, hX₂⟩, 
  rcases max_spec (g ∘ f) with ⟨X',hX'₁, hX'₂ ⟩, 
  erw [←hX'₁ , ←hX₁],
  from le_antisymm (hX'₂ _) (hg (hX₂ _)), 
end

/-- min commutes with composing by a monotone function-/
lemma min_compose_mono (f : α → β)(g : β → β')(hg : monotone g):
  g (min_val f) = min_val (g ∘ f) := 
begin
  rcases min_spec f with ⟨X, hX₁, hX₂⟩, 
  rcases min_spec (g ∘ f) with ⟨X',hX'₁, hX'₂⟩, 
  rw [←hX'₁, ←hX₁],
  from le_antisymm (hg (hX₂ _)) (hX'₂ _), 
end



/-- the max is at most a given upper bound for f -/
lemma max_le_ub {f : α → β}{b : β}(h_ub : ∀ x : α, f x ≤ b):
  max_val f ≤ b := 
by {cases max_spec f with X hX, rw [←hX.1], apply h_ub}

/-- a given lower bound for f is at most the max of f-/
lemma lb_le_max {f : α → β}(b : β)(h_lb : ∀ x : α, b ≤ f x):
   b ≤ max_val f := 
by {cases max_spec f with X hX, rw [←hX.1], apply h_lb, }

/-- the min of x is at most a given upper bound for f-/
lemma min_le_ub {f : α → β}{b : β}(h_ub : ∀ x : α, f x ≤ b):
  min_val f ≤ b := 
by {cases min_spec f with X hX, rw [←hX.1], apply h_ub}

/-- a given lower bound for x is at most the min of x-/
lemma lb_le_min {f : α → β}{b : β}(h_lb : ∀ x : α, b ≤ f x):
   b ≤ min_val f := 
by {cases min_spec f with X hX, rw [←hX.1], apply h_lb}

/-- an upper bound that is attained by f must be the max -/
lemma attained_ub_is_max (f : α → β)(a : α):
  (∀ x, f x ≤ f a) → max_val f = f a := 
begin
  intros h_ub, 
  rcases max_spec f with ⟨X, hX⟩, 
  apply le_antisymm (max_le_ub h_ub), 
  rw [←hX.1], apply hX.2, 
end

lemma attained_ub_is_max' (f : α → β)(a : α)(b : β):
  f a = b → (∀ x, f x ≤ b) → max_val f = b :=
λ hab hub, by {rw ←hab at hub ⊢, apply attained_ub_is_max, from hub}

/-- a lower bound attained by f must be the min -/
lemma attained_lb_is_min (f : α → β)(a : α):
  (∀ x, f a ≤ f x) → min_val f = f a  := 
begin
  intros h_lb, 
  rcases min_spec f with ⟨X, hX⟩, 
  refine le_antisymm _ (lb_le_min h_lb),
  rw [←hX.1], apply hX.2, 
end

lemma attained_lb_is_min' (f : α → β)(a : α)(b : β):
  f a = b → (∀ x, b ≤ f x) → min_val f = b :=
λ hab hub, by {rw ←hab at hub ⊢, apply attained_lb_is_min, from hub}

/-- the max of a constant function -/
lemma max_const (b : β): 
  max_val (λ (x : α), b) = b := 
by {rcases max_spec (λ (x : α), b) with ⟨x, hx⟩, rw ←hx.1 }

/-- the min of a constant function -/
lemma min_const (b : β): 
  min_val (λ (x : α), b) = b := 
by {rcases min_spec (λ (x : α), b) with ⟨x, hx⟩, rw ←hx.1 }


/-- given a bound f(x) ≤ f(x') for all x,x', a pair a,a' for which f(a) = f(a') determines
the max and min of f,f' respectively  -/
lemma minmax_eq_cert [nonempty α'][nonempty (fintype α')](f : α → β)(f' : α' → β):
  (∃ a a', f a = f' a') → (∀ x x', f x ≤ f' x') → max_val f = min_val f' := 
begin
  rintros ⟨a, a', heq⟩ hbound, 
  rcases max_spec f with ⟨x,hx⟩, 
  rcases min_spec f' with ⟨y,hy'⟩, 
  have hub := attained_ub_is_max' f a (f' a') heq (λ x, hbound x a'),
  have hlb := attained_lb_is_min' f' a' (f a) heq.symm (λ x', hbound a x'), 
  rw [hub, hlb, heq],
end

lemma max_compose_le_max [non_empt : nonempty α][nonempty (fintype α')](φ : α → α')(f : α' → β): 
  max_val (f ∘ φ) ≤ @max_val _ _ _ (nonempty.map φ non_empt) _ f := 
begin
  rcases max_spec (f ∘ φ) with ⟨a, ⟨ha₁, ha₂⟩⟩, 
  rcases @max_spec _ _ _ (nonempty.map φ non_empt) _ f with ⟨a', ⟨ha'₁, ha'₂⟩⟩, 
  rw [←ha₁, ←ha'₁],
  apply ha'₂,  
end

lemma min_le_min_compose [non_empt : nonempty α][nonempty (fintype α')](φ : α → α')(f : α' → β): 
  @min_val _ _ _ (nonempty.map φ non_empt) _ f  ≤ min_val (f ∘ φ) := 
begin
  rcases min_spec (f ∘ φ) with ⟨a, ⟨ha₁, ha₂⟩⟩, 
  rcases @min_spec _ _ _ (nonempty.map φ non_empt) _ f with ⟨a', ⟨ha'₁, ha'₂⟩⟩, 
  rw [←ha₁, ←ha'₁],
  apply ha'₂,  
end

instance prod_fin [nonempty (fintype α')]: nonempty (fintype (α × α')) := 
by {letI := classical.choice _inst_1, 
    letI := classical.choice _inst_5, 
    apply nonempty.intro, apply_instance, } 

/-- a bimonotone function of two maxima is a maximum over a product type -/
lemma max_zip [nonempty α'][nonempty (fintype α')](f : α → β)(f' : α' → β)(g : β × β → β')
                (g_mono : ∀ b₁ b₂ b₁' b₂', b₁ ≤ b₁' → b₂ ≤ b₂' → g ⟨b₁,b₂⟩ ≤ g ⟨b₁',b₂'⟩): 
  g ⟨max_val f, max_val f'⟩ = max_val (λ a : α × α', g ⟨f a.1,f' a.2⟩) :=
let f_prod := (λ a : α × α', g ⟨f a.1,f' a.2⟩) in 
begin
  rcases max_spec f with ⟨a, ⟨ha₁, ha₂⟩⟩, 
  rcases max_spec f' with ⟨a', ⟨ha'₁, ha'₂⟩⟩, 
  rcases max_spec f_prod with ⟨⟨x,x'⟩,⟨hx₁, hx₂⟩⟩, 
  rw [←ha₁,←ha'₁,←hx₁],
  apply le_antisymm,  
  from hx₂ ⟨a,a'⟩, apply g_mono, apply ha₂, apply ha'₂, 
end

/-- a bimonotone function of two minima is a minimum over a product type -/
lemma min_zip [nonempty α'][nonempty (fintype α')](f : α → β)(f' : α' → β)(g : β × β → β')
                (g_mono : ∀ b₁ b₂ b₁' b₂', b₁ ≤ b₁' → b₂ ≤ b₂' → g ⟨b₁,b₂⟩ ≤ g ⟨b₁',b₂'⟩): 
  g ⟨min_val f, min_val f'⟩ = min_val (λ a : α × α', g ⟨f a.1,f' a.2⟩) :=
let f_prod := (λ a : α × α', g ⟨f a.1,f' a.2⟩) in 
begin
  obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := min_spec f, 
  rcases min_spec f' with ⟨a', ⟨ha'₁, ha'₂⟩⟩, 
  rcases min_spec f_prod with ⟨⟨x,x'⟩,⟨hx₁, hx₂⟩⟩, 
  rw [←ha₁,←ha'₁,←hx₁],
  apply le_antisymm,  
  apply g_mono, apply ha₂, apply ha'₂, from hx₂ ⟨a,a'⟩,
end




end general_fintype 

section adding -- lemmas with a little more structure (eg addition) on β 

variables {α α' β : Type}[nonempty α][nonempty (fintype α)][nonempty α'][nonempty (fintype α')][linear_ordered_semiring β]

lemma max_add_commute (f : α → β)(s : β): 
  (max_val f) + s = max_val (λ x, f x + s) := 
begin
  set g : β → β := λ x, x + s with hg,
  have hg_mono : monotone g := 
    λ x y hxy, by {rw hg, dsimp only, apply add_le_add_right hxy},
  have := max_compose_mono f g hg_mono, 
  congr', 
end 

lemma min_add_commute (f : α → β)(s : β): 
  (min_val f) + s = min_val (λ x, f x + s) := 
begin
  set g : β → β := λ x, x + s with hg,
  have hg_mono : monotone g := 
    λ x y hxy, by {rw hg, dsimp only, apply add_le_add_right hxy},
  have := min_compose_mono f g hg_mono, 
  congr', 
end 

lemma sum_of_max (f : α → β)(f' : α' → β):
  max_val f + max_val f' = max_val (λ a : α × α', f a.1 + f' a.2) :=
max_zip f f' (λ (b : β × β), b.1+b.2) (λ _ _ _ _ h₁ h₂, add_le_add h₁ h₂) 
  
lemma sum_of_min (f : α → β)(f' : α' → β):
  min_val f + min_val f' = min_val (λ a : α × α', f a.1 + f' a.2) :=
min_zip f f' (λ (b : β × β), b.1+b.2) (λ _ _ _ _ h₁ h₂, add_le_add h₁ h₂) 



end adding 


/- sums, intersections, unions etc over finite types, as opposed to sets/finsets. 
emphasis is on being able to reindex -/


/-

variables {α β γ: Type}[fintype α](op: β → β → β)[is_commutative β op][is_associative β op]

/-- returns a list of elements of pairs (a,f(a)) for a in α -/
def as_list (f : α → β) : list (α × β) := 
  let s := (infer_instance : fintype α).elems.val in (s.map (λ a, (⟨a,f a⟩ : α × β))).to_list 

def val_list (f : α → β) : list β := 
  (as_list f).unzip.2  


/-- folds the commutative, associative operation op over the elements of β indexed by α 
starting at b -/
def fold (b : β)(f : α → β) : β := 
  let fs := (infer_instance : fintype α).elems in fs.fold op b f

/-- fintype folding can be written as a list folding (for induction)-/
lemma fold_eq_fold_list (b : β)(f : α → β) : 
  fold op b f = (as_list f).foldr (λ p q, op p.2 q) b := 
begin
  simp only [fold, as_list, finset.fold], 
  set ms := (multiset.map (λ (a : α), (a, f a)) (fintype.elems α).val), 
  have hl := ms.coe_to_list, rw ←hl, 
  have := multiset.coe_fold_r op b (val_list f),   --b ms.to_list,
  sorry,   
end









def Sum [add_comm_monoid β](f : α → β) : β := 
  fold (+) (0 : β) f 

def Prod [comm_monoid β](f : α → β) : β := 
  fold (*) (1 : β) f 

def Union (f : α → set γ) : set γ := 
  fold (∪) ∅ f 

def Inter (f : α → set γ) : set γ := 
  fold (∩) univ f 

lemma Inter_eq_setInter (f : α → set γ):
  Inter f = set.Inter f := 
begin
  rw  [Inter, fold_eq_fold_list],  
  --induction as_list f, 
  dsimp, sorry, 
end


-/



 /-
 
  def fin.induction {n : ℕ} {C : fin (n + 1) → Sort u_1} (h0 : C 0) 
                          (hs : Π (i : fin n), C (⇑fin.cast_succ i) → C i.succ) (i : fin (n + 1)) :
    C i

Define C i by induction on i : fin (n + 1) via induction on the underlying nat value. This function has two arguments: h0 handles the base case on C 0, and hs defines the inductive step using C i.cast_succ.
 -/ 



-- def list.foldr {α : Type u} {β : Type v} (f : α → β → β) (b : β) :
--list α → β


--def union_over {n : ℕ}(Xs : fin n → set U) : set U := 
--  finset.fold (λ a b, a ∪ b) (∅ : set U) Xs (fin n)














