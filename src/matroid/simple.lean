import .loop

noncomputable theory
open_locale classical

open set
namespace matroid

variables {E E' : Type*} [finite E] [finite E'] {N M : matroid E} {e f : E} {X Y Z S T : set E}

section simple

/-- the property of a set not containing any loops -/
def loopless_set (M : matroid E) (X : set E) : Prop := ∀ e ∈ X, M.nonloop e
  
/-- the property of a matroid having no loops -/
@[reducible] def loopless (M : matroid E) : Prop := M.loopless_set univ 

lemma is_loopless_def {M : matroid E} :
  M.loopless ↔ M.loopless_set univ :=
iff.rfl

lemma loopless_set.subset (h : M.loopless_set Y) (hXY : X ⊆ Y) : M.loopless_set X :=
subset_trans hXY h 

lemma loopless_set.nonloop_of_mem (h : M.loopless_set X) (he : e ∈ X) : M.nonloop e := 
h e he 

lemma loopless_set.indep_of_mem (h : M.loopless_set X) (he : e ∈ X) : M.indep {e} := 
by { rw ←nonloop_iff_indep, exact h.nonloop_of_mem he }

/-- the property of a set containing no loops or parallel pairs -/
def simple_set (M : matroid E) (X : set E) : Prop := ∀ e f ∈ X, M.indep {e,f}

/-- the property of a matroid having no loops or parallel pairs -/
@[reducible] def simple (M : matroid E) : Prop := M.simple_set univ 

lemma simple_iff_forall_pair_indep : M.simple ↔ ∀ e f, M.indep {e,f} := 
⟨λ h e f, h e (mem_univ e) f (mem_univ f), λ h e he f hf, h e f⟩    

lemma simple_set.subset (h : M.simple_set Y) (hXY : X ⊆ Y) : M.simple_set X := 
λ e he f hf, h e (hXY he) f (hXY hf)  

lemma simple_set.pair_indep_of_mem (h : M.simple_set X) (he : e ∈ X) (hf : f ∈ X) : M.indep {e,f} :=
h e he f hf 

lemma simple_set.loopless_set (h : M.simple_set X) : M.loopless_set X :=
begin
  intros x hx, 
  rw [nonloop_iff_indep, ←pair_eq_singleton], 
  exact h.pair_indep_of_mem hx hx, 
end 

lemma simple_set.nonloop_of_mem (h : M.simple_set X) (he : e ∈ X) : ¬M.loop e :=
h.loopless_set.nonloop_of_mem he 

lemma simple_set.indep_of_card_le_two (h : M.simple_set X) (hX : X.ncard ≤ 2) :
  M.indep X := 
begin
  obtain (h2 | hlt2) := eq_or_lt_of_le hX, 
  { obtain ⟨x,y,-,rfl⟩ := ncard_eq_two.mp h2,
    exact h x (by simp) y (by simp) },
  obtain (h1 | hlt1) := eq_or_lt_of_le (nat.lt_succ_iff.mp hlt2), 
  { obtain ⟨a,rfl⟩ := ncard_eq_one.mp h1, 
    rw [←nonloop_iff_indep],
    exact h.nonloop_of_mem (mem_singleton _) },
  convert M.empty_indep, 
  simpa using hlt1, 
end

lemma simple_set.eq_pf_pair_r_one (h : M.simple_set X) (he : e ∈ X) (hf : f ∈ X) 
  (hef : M.r {e,f} = 1) : 
  e = f :=
begin
  rw [(h.pair_indep_of_mem he hf).r] at hef, 
  exact ncard_le_one_iff.mp hef.le (by simp) (by simp), 
end

-- lemma simple_set_iff_cl_inj_on : 
--   M.simple_set X ↔ M.loopless_set X ∧ inj_on (λ e, M.cl {e}) X := 
-- begin
--   refine ⟨λ h, ⟨h.loopless_set, λ e he f hf (hef : M.cl {e} = M.cl {f}), _⟩, λ h, _⟩,
--   { have he' := singleton_subset_iff.mp ((M.subset_cl {e}).trans hef.subset), 
--     rw (h.loopless_set.indep_of_mem hf).mem_cl_iff at he',
--     exact he'.elim id (λ hi, (hi (h e he f hf)).elim) },


--   intros e he f hf, 
--   have hcl : f ∉ M.cl {e}, 
--   { intro hfe, },
--   rw [pair_comm],
--   exact ((h.1.nonloop_of_mem he).indep.not_mem_cl_iff.mp hcl).2, 



--   -- have := h.1.indep_of_mem he, 
--   -- have := this.not_mem_cl_iff, 
--   -- rw h.2 he hf,
--   -- { rw [pair_eq_singleton, ←nonloop_iff_indep], 
--   --   exact h.1.nonloop_of_mem hf }, 
  
-- end 

end simple 

section parallel 

def parallel (M : matroid E) (e f : E) : Prop := M.cl {e} = M.cl {f}  

-- lemma parallel_self (M : matroid E) (x : E) : M.parallel x x := by rw [parallel]

-- lemma parallel_symm (M : matroid E) : M.parallel e f ↔ M.parallel f e := 
-- by { rw [parallel, eq_comm], refl }

-- lemma parallel_trans 

-- infix ` ~ ` :75 :=  matroid.parallel 


-- lemma parallel.loops_or_nonloops (h : M.parallel e f) : 
  



-- lemma parallel_iff :
--   M.parallel 


end parallel 

end matroid


