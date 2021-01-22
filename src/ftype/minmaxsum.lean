-- Experimental/broken - nothing relies on this. 

import .basic .induction .single 
----------------------------------------------------------------
open_locale classical 
noncomputable theory 


-- Lemmas applying for a general nonempty fintype 
-- TODO - lemmas about folding, so sum etc is also subsumed 

section general_fintype 

variables {α α' β β': Type}[fintype α][nonempty α][linear_order β][linear_order β']

lemma exists_max (f : α → β): 
  ∃ x, ∀ y, f y ≤ f x := 
fintype.exists_max f

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

/-- taking a max over one type is equivalent to taking one over another, 
given a bijection between them -/
lemma max_reindex (φ : α → α')(hφ : function.bijective φ)(f : α' → β):
  max_val (f ∘ φ) = @max_val _ _ (fintype.of_bijective φ hφ) (nonempty.map φ _inst_2) _ f := 
begin
  rcases @max_spec _ _ (fintype.of_bijective φ hφ) (nonempty.map φ _inst_2) _ f 
    with ⟨x', ⟨hx'1, hx'2⟩⟩, 
  rcases max_spec (f ∘ φ) with ⟨x, ⟨hx1, hx2⟩ ⟩, 
  rw [←hx1, ←hx'1], 
  apply le_antisymm (hx'2 _), 
  cases hφ.2 x' with z hz,
  rw ←hz, apply hx2, 
end

/-- taking a min over one type is equivalent to taking one over another, 
given a bijection between them -/
lemma min_reindex (φ : α → α')(hφ : function.bijective φ)(f : α' → β):
  min_val (f ∘ φ) = @min_val _ _ (fintype.of_bijective φ hφ) (nonempty.map φ _inst_2) _ f := 
begin
  rcases @min_spec _ _ (fintype.of_bijective φ hφ) (nonempty.map φ _inst_2) _ f 
    with ⟨x', ⟨hx'1, hx'2⟩⟩, 
  rcases min_spec (f ∘ φ) with ⟨x, ⟨hx1, hx2⟩ ⟩, 
  rw [←hx1, ←hx'1], 
  refine le_antisymm _ (hx'2 _), 
  cases hφ.2 x' with z hz,
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

end general_fintype 

section adding -- lemmas with a little more structure (eg addition) on β 

variables {α β : Type}[fintype α][nonempty α][linear_ordered_semiring β]

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

end adding 















