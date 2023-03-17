import order.lattice 
import order.boolean_algebra

universe u 

class boolalg_ext_lemmas
  (T : Type*) (E : Type*) 
  [has_mem E T] 
  [has_sup T] 
  [has_inf T]
  [has_sdiff T]
  [has_bot T]
  [has_le T]
  [has_lt T]
   :=
  (simpl_eq : ∀ {A B : T}, A = B ↔ A ≤ B ∧ B ≤ A)
  (simpl_lt : ∀ {A B : T}, A < B ↔ A ≤ B ∧ ¬ B ≤ A)
  (ext_bot : ∀ {e}, e ∈ (⊥ : T) ↔ false)
  (ext_sdiff : ∀ {A B : T} e, e ∈ A \ B ↔ e ∈ A ∧ ¬ e ∈ B)
  (ext_le : ∀ {A B : T}, A ≤ B ↔ ∀ e, e ∈ A → e ∈ B) 
  (ext_meet : ∀ {A B : T} {e}, e ∈ (A ⊔ B) ↔ e ∈ A ∨ e ∈ B)
  (ext_join : ∀ {A B : T} {e}, e ∈ (A ⊓ B) ↔ e ∈ A ∧ e ∈ B)

class boolalg_ext_lemmas_compl
  (T : Type*) (E : Type*)
  [has_compl T]
  [has_mem E T] :=
  (ext_compl : ∀ {A : T} {e}, e ∈ Aᶜ ↔ ¬ e ∈ A)

class boolalg_ext_lemmas_top
  (T : Type*) (E : Type*)
  [has_mem E T]
  [has_top T] :=
  (ext_top : ∀ {e}, e ∈ (⊤ : T) ↔ true)
