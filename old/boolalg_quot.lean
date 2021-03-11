import tactic.ext
--import tactic.ring 
import tactic.linarith
import tactic.tidy 
import tactic 
import boolalg 
local attribute [instance] classical.prop_decidable


namespace boolalg 

def equivalence_closed (A : boolalg){r : single A → single A → Prop} (hr : equivalence r) : A → Prop := 
  λ X, ∀ e f : single A, (e:A) ⊆ X → r e f → (f:A) ⊆ X 

def quotient_alg (A : boolalg) {r : single A → single A → Prop} (hr : equivalence r) : boolalg := 
{ 
  member := {X: A // equivalence_closed A hr X},
  bot := ⟨⊥, fun X e f he ref, false.elim (sorry : ¬e ⊆ ⊥)⟩,
  top := ⟨⊤, sorry⟩, 
  inter := λ X Y, ⟨X.1 ∩ Y.1, sorry ⟩, 
  union := _,
  compl := _,
  size := _,
  subset := _,
  size_bot_ax := _,
  size_nonneg_ax := _,
  size_modular_ax := _,
  single_subset'_ax := _,
  inter_comm_ax := _,
  union_comm_ax := _,
  union_distrib_right_ax := _,
  inter_distrib_right_ax := _,
  inter_top_ax := _,
  union_bot_ax := _,
  union_compl_self := _,
  inter_compl_ax := _,
  inter_subset_ax := _,
  inter_assoc_ax := _,
  union_assoc_ax := _ }


end boolalg 