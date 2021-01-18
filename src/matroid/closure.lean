import ftype.basic ftype.induction ftype.collections .rankfun .indep 
open ftype 

local attribute [instance] classical.prop_decidable
noncomputable theory 

variables {U : ftype}

lemma cl.monotone (M : clfun U){X Y : set U} :
  X ⊆ Y → M.cl X ⊆ M.cl Y :=
  λ h, M.cl3 _ _ h

lemma cl.subset_union (M : clfun U)(X Y : set U) :
  M.cl X ∪ M.cl Y ⊆ M.cl (X ∪ Y) :=
  union_is_ub (M.cl3 _ _ (subset_union_left X Y)) (M.cl3 _ _ (subset_union_right X Y))
  

lemma cl.cl_union_both (M : clfun U)(X Y : set U) :
  M.cl (X ∪ Y) = M.cl(M.cl X ∪ M.cl Y) :=
  begin
    apply subset_antisymm, 
    from cl.monotone M (union_subset_pairs (M.cl1 X) (M.cl1 Y)),
    have := cl.monotone M (cl.subset_union M X Y),
    rw M.cl2 at this, assumption
  end


lemma cl.union_pair {M : clfun U}{X Y : set U} (Z: set U): 
  M.cl X = M.cl Y → M.cl (X ∪ Z) = M.cl (Y ∪ Z) :=
  λ h, by rw [cl.cl_union_both _ X, cl.cl_union_both _ Y, h]

lemma cl.cl_union_left (M : clfun U)(X Y : set U) :
  M.cl (M.cl X ∪ Y) = M.cl (X ∪ Y)  :=
  cl.union_pair Y (M.cl2 X)

def cl.is_indep (M : clfun U) : set U → Prop := 
  λ I, ∀ (e:U), e ∈ I → M.cl (I \ e) ≠ M.cl I 

lemma cl.satisfies_I1 (M : clfun U) : 
  satisfies_I1 (cl.is_indep M) :=
  λ e h, false.elim (nonelem_bot e h)
  
lemma cl.satisfies_I2 (M : clfun U) : 
  satisfies_I2 (cl.is_indep M) :=
  begin
    apply weak_I2_to_I2 (λ X, cl.is_indep M X), 
    intros I e heI hIe,
    by_contra h, unfold cl.is_indep at h, push_neg at h, 
    rcases h with ⟨f, ⟨hfI, hIfcl⟩⟩, 
    have := cl.union_pair (e: set U) hIfcl, 
    rw exchange_comm hfI heI at this, 
    from hIe f (elem_of_elem_of_subset hfI (subset_union_left I e)) this, 
  end 

lemma cl.satisfies_I3 (M : clfun U) : 
  satisfies_I3 (cl.is_indep M) :=
  begin
    sorry 
  end

def clfun_to_indep_family (M : clfun U) : indep_family U := 
⟨cl.is_indep M, cl.satisfies_I1 M, cl.satisfies_I2 M, cl.satisfies_I3 M⟩

def clfun_to_rankfun (M : clfun U) : rankfun U := 
  indep_family_to_rankfun (clfun_to_indep_family M)
