import tactic 

example {M : Type*} 
[ordered_cancel_add_comm_monoid M] 
[canonically_ordered_add_monoid M] 
(x y z : M): 
  false :=
begin
  have : 0 ≤ x := zero_le x, -- fails 
end
