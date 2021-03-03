import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax
import .parallel 

noncomputable theory 
open_locale classical 

open set 
namespace matroid 

variables {U V : Type}[fintype U][fintype V]

