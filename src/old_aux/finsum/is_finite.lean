
import tactic 

open_locale classical 

universes u v

variables {α : Type*} {β : Type*}



instance is_finite_of_subset_type [i : nonempty (fintype α)] {S : set α} : nonempty (fintype S) := 
by {letI := classical.choice i, exact nonempty.intro (by apply_instance),  }

instance is_finite_of_subtype [i : nonempty (fintype α)] {P : α → Prop} : nonempty (fintype {x // P x}) := 
by {letI := classical.choice i, exact nonempty.intro (by apply_instance),  }

instance is_finite_of_set_type [i : nonempty (fintype α)] : nonempty (fintype (set α)) := 
by {letI := classical.choice i, exact nonempty.intro (by apply_instance),  }

instance is_finite_option_type [i : nonempty (fintype α)] : 
  nonempty (fintype (option α)) := 
by {letI := classical.choice i, exact nonempty.intro (by apply_instance),  }

--instance is_finite_of_fn [i : nonempty (fintype α)] [j : nonempty (fintype β)] : nonempty (fintype )