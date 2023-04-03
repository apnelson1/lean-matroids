-- import .inter 
-- import ..constructions.direct_sum
-- import ..equiv
-- import algebra.big_operators.finprod

-- open_locale classical 
-- open_locale big_operators
-- open set 


-- variables {ι E : Type*} [finite ι] [finite E] 

-- def matroid_of_rel (M : matroid E) (S : ι → set E) :
--   matroid ι := 
-- matroid_of_indep 
-- (λ I, ∃ f : I ↪ E, (M.indep (range f)) ∧ ∀ i, f i ∈ S i ) 
-- (begin
--   use [∅, ⟨is_empty_elim, is_empty_elim⟩],
--   refine ⟨_,by simp⟩,   
--   simpa [range_eq_empty] using M.empty_indep,  
-- end) 
-- (begin
--   rintro I J hIJ ⟨fJ, hfJ, hf⟩, 
--   exact ⟨(subtype.imp_embedding _ _ hIJ).trans fJ, hfJ.subset (range_comp_subset_range _ _ ), 
--       λ i, hf (subtype.imp_embedding _ _ hIJ i)⟩,
-- end) 
-- (begin
--   rintro I J ⟨fI, hI, hfI⟩ ⟨fJ, hJ, hfJ⟩ hIJ, 
--   -- have : I.ncard = (range fI).ncard, 
--   simp_rw [ncard_eq_nat_card_subtype, ←ncard_range_of_injective fI.injective, 
--     ←ncard_range_of_injective fJ.injective] at hIJ, 
--   obtain ⟨e,⟨⟨j,rfl⟩ , h₂⟩⟩ := exists_mem_not_mem_of_ncard_lt_ncard hIJ, 
--   refine ⟨j, j.2, _, _⟩, 


-- end)

