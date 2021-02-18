import prelim.embed prelim.minmax set_tactic.solver
import .minor 

open_locale classical 
noncomputable theory

open matroid set 


variables {U V : Type}[fintype U][fintype V]

def matroid.is_iso_to_minor_of (N : matroid V)(M : matroid U) := 
  ∃ (M' : matroid_in U), M'.is_minor M ∧ M'.is_isom N 

/-- N is isomorphic to a minor of M iff there is a suitable injection and contract set. This is DTT hell, but hopefully 
only has to be done once, and is in practice how one would show M has an N-minor -/
lemma iso_to_minor_of_iff_exists_map {N : matroid V}{M : matroid U}:
  N.is_iso_to_minor_of M ↔ ∃ (φ : V ↪ U)(C : set U), (set.range φ) ∩ C = ∅ 
                         ∧ ∀ X, N.r X = M.r (φ '' X ∪ C) - M.r C := 
begin
  refine ⟨λ h, _, λ h, _⟩,
  begin
    rcases h with ⟨M',⟨p⟩, ⟨eqv, h⟩⟩,
    have hEC := p.E_inter_C, 
    have hED := p.E_inter_D, 
    rcases p with ⟨C,D,hi,hu,rfl⟩, 
    refine ⟨eqv.symm.to_embedding.trans (function.embedding.subtype _),  C, _,λ X, _⟩,
    { dsimp only at *, convert hEC,
      ext, 
      simp only [equiv.to_embedding_apply, function.embedding.coe_subtype, image_univ,
        function.embedding.trans_apply, mem_range], 
      split, rintros ⟨y,rfl⟩, exact (eqv.symm y).2, 
      exact λ hx, ⟨eqv ⟨x,hx⟩, by simp⟩}, 
    convert h (eqv ⁻¹' X), simp, 
    ext, 
    simp only [mem_image, equiv.to_embedding_apply, function.embedding.coe_subtype, 
      function.embedding.trans_apply, mem_diff], 
    split, rintros ⟨y,⟨hy, rfl⟩⟩, split, unfold_coes, simpa, 
    { apply nonmem_of_mem_disjoint ((eqv.symm y).2) hED}, 
    rintros ⟨hx,-⟩,  unfold_coes at hx, 
    simp only [mem_image, equiv.to_fun_as_coe, set_coe.exists, exists_and_distrib_right, 
                exists_eq_right, mem_preimage, subtype.coe_mk] at hx,
    rcases hx with ⟨hx,h'⟩, 
    exact ⟨eqv ⟨x,hx⟩,⟨h',by simp⟩⟩, 
  end, 
  rcases h with ⟨φ, C, hC, hr⟩, 
  
  set E := set.range φ with hE, set D := (E ∪ C)ᶜ with hD,  
  set M₀ : matroid_in U := (M : matroid_in U) / C \ D with hM₀,
  refine ⟨M₀, matroid_in.con_del_is_minor _ _ _,nonempty.intro _, ⟩,
  have hEM: set.range φ = M₀.E , 
  { rw [disjoint_iff_subset_compl, subset_iff_inter, inter_comm] at hC, 
    simp only [hM₀, ←hE, hD, hC, compl_compl, univ_inter, inter_distrib_left] with msimp,   
    simp,},
  set eqv : M₀.E ≃ V := 
    (equiv.trans (equiv.set.range φ φ.inj') (equiv.set.of_eq hEM)).symm with heqv, 
  refine ⟨eqv,λ X, _⟩, 
  have hX : ↑X ⊆ M₀.E := coe_set_is_subset _, 
  
  simp only [hr, hM₀, heqv] with msimp,  convert rfl,
  have hXD : (↑X ∩ Dᶜ) = X,
  { simp_rw [←subset_iff_inter,hD,compl_compl, hE, hEM],  
    apply subset_union_of_subset_left hX _, },
  rw hXD, 
     
  ext, simp only [mem_image, set_coe.exists], 
  refine ⟨λ hx, _, λ h, _⟩,
  have hxE := mem_of_mem_of_subset hx hX, 
  refine ⟨eqv ⟨x, hxE,⟩,⟨⟨x,hxE,⟨_,_⟩ ⟩,_⟩⟩, 
  { rcases hx with ⟨y, ⟨hy, rfl⟩⟩, simpa,  },
  { simp only [heqv, equiv.coe_fn_symm_mk, function.comp_app, 
                  equiv.set.of_eq_symm_apply, subtype.coe_mk], },
  { exact equiv.set.apply_range_symm φ φ.inj' _}, 

  rcases h with ⟨h_w,⟨y, h', hy, rfl⟩, rfl⟩, 
  simp only [equiv.symm_trans_apply, equiv.set.of_eq_symm_apply, subtype.coe_mk], 
  simp_rw (equiv.set.apply_range_symm φ φ.inj' _),  
  unfold_coes, simp [mem_image], refine ⟨h',hy⟩,    
end


