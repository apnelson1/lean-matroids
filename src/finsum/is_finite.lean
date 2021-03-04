
import tactic 

open_locale classical 

variables {α : Type*}


instance is_finite_of_subset_type [i : nonempty (fintype α)]{S : set α} : nonempty (fintype S) := 
by {letI := classical.choice i, exact nonempty.intro (by apply_instance),  }

instance is_finite_of_subtype [i : nonempty (fintype α)]{P : α → Prop} : nonempty (fintype {x // P x}) := 
by {letI := classical.choice i, exact nonempty.intro (by apply_instance),  }

instance is_finite_of_set_type [i : nonempty (fintype α)] : nonempty (fintype (set α)) := 
by {letI := classical.choice i, exact nonempty.intro (by apply_instance),  }