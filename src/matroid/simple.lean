import prelim.collections prelim.embed prelim.fincard prelim.induction prelim.minmax
import .parallel matroid.submatroid.projection

noncomputable theory 
open_locale classical 

open set 
namespace matroid 

variables {α β : Type*} [fintype α] [fintype β] {N M : matroid α} {e f : α} {S X : set α}

section simple 

/-- the property of a set not containing any loops -/
def is_loopless_set (M : matroid α) (S : set α) :=
  ∀ X ⊆ S, fincard X ≤ 1 → M.is_indep X

/-- the property of a matroid having no loops -/
def is_loopless (M : matroid α) := 
  is_loopless_set M univ 

lemma loopless_iff_univ_loopless {M : matroid α} : 
  is_loopless M ↔ is_loopless_set M univ := 
iff.rfl 

/-- the property of a set containing no loops or parallel pairs -/
def is_simple_set (M : matroid α) (S : set α) :=
  ∀ X ⊆ S, fincard X ≤ 2 → M.is_indep X 

lemma simple_of_subset_simple {M : matroid α} {S T : set α} (hT : M.is_simple_set T) (hST : S ⊆ T) :
  M.is_simple_set S := 
λ X hX, hT X (subset.trans hX hST)

/-- the property of a matroid containing no loops or parallel pairs -/
def is_simple (M : matroid α) :=
  is_simple_set M univ 

lemma simple_set_iff_r : 
  M.is_simple_set S ↔ ∀ X ⊆ S, fincard X ≤ 2 → fincard X ≤ M.r X :=
by simp_rw [is_simple_set, indep_iff_fincard_le_r]

lemma rank_subset_simple (h : M.is_simple) (hX : fincard X ≤ 2) :
  M.r X = fincard X := 
h X (subset_univ _) hX

lemma rank_singleton_of_simple (h : M.is_simple) (e : α) : 
  M.r {e} = 1 :=
by {rw [←fincard_singleton e, ← indep_iff_r], apply h _ (subset_univ _), rw fincard_singleton, norm_num }

lemma rank_pair_of_simple (h : M.is_simple) (hef : e ≠ f) : 
  M.r {e,f} = 2 :=
by rw [indep_iff_r.mp (h {e,f} (subset_univ _) (by rw fincard_pair hef)), fincard_pair hef]

lemma rank_mem_simple_set (h : M.is_simple_set S) (he : e ∈ S) : 
  M.r {e} = 1 :=
begin
  rw [←fincard_singleton e, ← indep_iff_r], 
  apply h _ (singleton_subset_iff.mpr he), 
  rw fincard_singleton, 
  norm_num,
end 

lemma rank_pair_of_simple_set (h : M.is_simple_set S) (hef : e ≠ f) (he : e ∈ S) (hf : f ∈ S): 
  M.r {e,f} = 2 :=
begin
  rw [indep_iff_r.mp (h {e,f} _ (by rw fincard_pair hef)), fincard_pair hef], 
  rw ← singleton_subset_iff at he hf,   
  convert union_subset he hf, 
end 

lemma rank_subset_simple_set (h : M.is_simple_set S) (hX : X ⊆ S) (hX' : fincard X ≤ 2):
  M.r X = fincard X :=
by convert h X hX hX'

lemma rank_subset_simple_set_lb (h : M.is_simple_set S) (hX : X ⊆ S): 
  min 2 (fincard X) ≤ M.r X := 
begin
  cases le_or_lt (fincard X) 2 with h1 h2, 
  { rwa [min_eq_right h1, rank_subset_simple_set h hX]}, 
  rw min_eq_left (le_of_lt h2), 
  obtain ⟨X₀, hX₀, hX₀'⟩ := has_subset_of_fincard (by norm_num : (0 : ℤ) ≤ 2) (le_of_lt h2), 
  rw [← hX₀', ← (rank_subset_simple_set h (subset.trans hX₀ hX) (le_of_eq hX₀'))],
  exact rank_mono _ hX₀, 
end 

lemma rank_subset_simple_lb (h : M.is_simple) (X : set α): 
  min 2 (fincard X) ≤ M.r X := 
rank_subset_simple_set_lb h (subset_univ _)

lemma eq_of_rank_one_simple (h : M.is_simple) (hef : M.r {e,f} = 1) : 
  e = f := 
by_contra (λ hn, by {rw rank_pair_of_simple h hn at hef, norm_num at hef })

lemma eq_of_rank_le_one_simple (h : M.is_simple) (hef : M.r {e,f} ≤ 1) : 
  e = f := 
begin
  refine eq_of_rank_one_simple h (le_antisymm hef _), 
  rw ← rank_singleton_of_simple h e,
  apply rank_mono, 
  simp,  
end

lemma loopless_of_simple (hM : M.is_simple) :
  M.is_loopless := 
λ X hX hs, hM X hX (by linarith)

lemma simple_iff_univ_simple {M : matroid α} : 
  is_simple M ↔ is_simple_set M univ := 
iff.rfl 

def simple_set (M : matroid α) := {X : set α // M.is_simple_set X} 

instance simple_set_nonempty {M : matroid α} : nonempty M.simple_set := 
  ⟨⟨∅, λ X hX _, by {rw eq_empty_of_subset_empty hX, apply empty_indep, }⟩⟩ 

instance simple_set_fintype {M : matroid α} : fintype M.simple_set := 
  by {unfold simple_set, apply_instance,}

instance {M : matroid α} : has_coe M.simple_set (set α) := ⟨subtype.val⟩ 

def simple_subset_of (M : matroid α) (S : set α) := {X : set α // M.is_simple_set X ∧ X ⊆ S} 

instance simple_subset.ne {M : matroid α} {S : set α} : nonempty (M.simple_subset_of S) := 
  ⟨⟨∅, ⟨λ X hX _, by {rw eq_empty_of_subset_empty hX, apply empty_indep, }, empty_subset _⟩ ⟩⟩ 

instance simple_subset.fin {M : matroid α} {S : set α} : fintype (M.simple_subset_of S) := 
by {unfold simple_subset_of, apply_instance,}

instance simple_subset.coe {M : matroid α} {S : set α} : 
  has_coe (M.simple_subset_of S) (set α) := ⟨subtype.val⟩ 

lemma simple_of_indep {M : matroid α} {I : set α} (hI : M.is_indep I): 
  M.is_simple_set I := 
λ _ hX _, indep_of_subset_indep hX hI

lemma loopless_set_iff_all_nonloops {M : matroid α} {S : set α} : 
  M.is_loopless_set S ↔ ∀ e ∈ S, M.is_nonloop e :=
begin
  simp_rw [nonloop_iff_r, is_loopless_set, fincard_le_one_iff_empty_or_singleton, indep_iff_r],
  refine ⟨λ h, λ e he ,_  , λ h, λ X hX h', _⟩, 
  {rw ← fincard_singleton e, exact h _ (singleton_subset_iff.mpr he) (or.inr ⟨e, rfl⟩)},  
  rcases h' with (rfl | ⟨e,rfl⟩), simp, 
  rw [fincard_singleton, h e (singleton_subset_iff.mp hX)],  
end

lemma loopless_set_iff_subset_nonloops {M : matroid α} {S : set α} :
  M.is_loopless_set S ↔ S ⊆ M.nonloops := 
by {rw [loopless_set_iff_all_nonloops, nonloops], tauto}

lemma loopless_iff_all_nonloops {M : matroid α} :
  M.is_loopless ↔ ∀ e, M.is_nonloop e :=
by {rw [loopless_iff_univ_loopless, loopless_set_iff_all_nonloops], tauto}

lemma nonloop_of_mem_loopless_set {M : matroid α} {S : set α} {e : α}
(h : M.is_loopless_set S) (he : e ∈ S) :
  M.is_nonloop e := 
by {rw loopless_set_iff_all_nonloops at h, tauto, }

lemma nonloop_of_simple {M : matroid α} (hM : M.is_simple) (e : α) : 
  M.is_nonloop e :=
nonloop_of_mem_loopless_set (loopless_of_simple hM) (mem_univ e)

lemma exists_loop_of_not_loopless_set {M : matroid α} {S : set α} (hS : ¬M.is_loopless_set S) : 
  ∃ e ∈ S, M.is_loop e :=
begin
  by_contra hn, 
  simp_rw [loopless_set_iff_all_nonloops, nonloop_iff_not_loop] at hS, 
  push_neg at hS hn,
  obtain ⟨e,⟨he,he'⟩⟩ := hS, 
  exact hn e he he',    
end 

lemma exists_loop_of_not_loopless {M : matroid α} (h : ¬M.is_loopless) : 
  ∃ e, M.is_loop e := 
let ⟨e,_,h'⟩ := exists_loop_of_not_loopless_set h in ⟨e,h'⟩ 

lemma nonloop_of_loopless {M : matroid α} (e : α) (h : M.is_loopless) :
  M.is_nonloop e := 
by {rw loopless_iff_all_nonloops at h, tauto, }

lemma rank_single_of_loopless {M : matroid α} (h : M.is_loopless) (e : α) : 
  M.r {e} = 1 := 
by {rw [←nonloop_iff_r], apply nonloop_of_loopless e h,  }

lemma simple_set_iff_no_loops_or_parallel_pairs {M : matroid α} {S : set α} :
  M.is_simple_set S ↔ M.is_loopless_set S ∧ ∀ (e f ∈ S), M.parallel e f → e = f := 
begin
  refine ⟨λ h, ⟨λ X hXS hX, h X hXS (by linarith [hX]),λ e f he hf hef, by_contra (λ hn, _)⟩,
  λ h, λ X hXS hX, _⟩, 
  { rcases hef with ⟨he,hf,hef⟩, 
    have hef' := fincard_pair hn, 
    linarith [r_indep (h {e,f} (λ x, by {simp, rintros (rfl | rfl); assumption, }) (by linarith))]},
  rcases int.nonneg_le_two_iff (fincard_nonneg X) hX with (h0 | h1 | h2), 
  { rw fincard_zero_iff_empty at h0, rw h0, apply M.empty_indep, },
  { obtain ⟨e,rfl⟩ := fincard_one_iff_eq_singleton.mp h1, 
    rw singleton_subset_iff at hXS, 
    exact nonloop_iff_indep.mp (nonloop_of_mem_loopless_set h.1 hXS), },
  rcases fincard_eq_two_iff_pair.mp h2 with ⟨e,f,hef,rfl⟩, 
  by_contra hn, 
  cases pair_subset_iff.mp hXS with he hf, 
  
  suffices heq : e = f, rw [heq, pair_eq_singleton, fincard_singleton] at h2, norm_num at h2, 
  apply h.2 e f he hf, rw parallel_iff_dep _ _, right, 
    rwa [←dep_iff_not_indep] at hn, 
  all_goals {apply nonloop_of_mem_loopless_set h.1, assumption,  },
end

lemma simple_iff_no_loops_or_parallel_pairs {M : matroid α} :
  M.is_simple ↔ M.is_loopless ∧ ∀ (e f : α), M.parallel e f → e = f :=
by {rw [simple_iff_univ_simple, simple_set_iff_no_loops_or_parallel_pairs], tidy, }  

lemma simple_set_exchange (hS : M.is_simple_set S) (he : e ∈ S) (hp : M.parallel e f) : 
  M.is_simple_set (S \ {e} ∪ {f}) := 
begin
  rw [simple_set_iff_no_loops_or_parallel_pairs, loopless_set_iff_all_nonloops] at ⊢ hS,  
  simp only [mem_union_iff, mem_diff, mem_singleton_iff, mem_singleton_iff], 
  refine ⟨λ x hxS, _, λ x y hxS hyS hxy, _⟩, 
  { obtain (⟨hxS, -⟩ | rfl) := hxS, exact hS.1 x hxS, exact hp.nonloop_right},
  obtain (⟨hxS, hxe⟩ | rfl) := hxS; obtain (⟨hyS, hye⟩ | rfl) := hyS, 
  { exact hS.2 _ _ hxS hyS hxy},
  { exact false.elim ((ne.symm hxe) (hS.2 e x he hxS (hp.trans hxy.symm)))},  
  { exact false.elim ((ne.symm hye) (hS.2 e y he hyS (hp.trans hxy)))}, 
  refl, 
end

lemma simple_set_exchange' (hS : M.is_simple_set S) (hf : f ∈ S) (hp : M.parallel e f) : 
  M.is_simple_set ((S ∪ {e}) \ {f}) := 
begin
  rcases em (e = f) with (rfl | hef),  
  rw [union_mem_singleton hf], 
  exact simple_of_subset_simple hS (diff_subset _ _), 
  rw ← exchange_comm (ne.symm hef), 
  exact simple_set_exchange hS hf hp.symm, 
end

lemma loopify_simple_set_of_simple_set (hS : M.is_simple_set S) (hX : disjoint S X): 
  (M ⟍ X).is_simple_set S := 
begin
  intros Y hY hfincard, 
  rw indep_loopify_iff, 
  refine ⟨hS Y hY hfincard, _⟩, 
  rw [← disjoint_iff_inter_eq_empty], 
  exact disjoint_of_subset_left hY hX,  
end

lemma loopify_simple_iff_simple_disjoint : 
  (M ⟍ X).is_simple_set S ↔ M.is_simple_set S ∧ disjoint S X := 
begin
  refine ⟨λ h, ⟨ λ X hX hfincard, _ ,_⟩, λ h, loopify_simple_set_of_simple_set h.1 h.2⟩, 
  { exact indep_of_loopify_indep (h X hX hfincard)},
  by_contra hn, 
  obtain ⟨e, hx, hx'⟩ :=  not_disjoint_iff.mp hn, 
  simp_rw [simple_set_iff_no_loops_or_parallel_pairs, loopless_set_iff_all_nonloops,
    nonloop_iff_not_loop] at h, 
  exact h.1 e hx (loop_of_loopify _ hx'),  
end


/- The simple matroid associated with M (simplification of M). Its elements are the parallel classes
 of M, and the rank of a set of parallel classes is the rank in M of their union. -/
def si (M : matroid α) : matroid (M.parallel_class) := 
{ r := λ X, M.r (union_parallel_classes X),
  R0 := λ X, by {apply M.R0 },
  R1 := λ X, begin 
    let f := choose_transversal M, 
    simp only [rank_img_transversal f, ←fincard_image_transversal f],
    apply M.R1, 
  end,
  R2 := λ X Y hXY, begin
    dsimp only, 
    convert M.rank_mono (inter_subset_right _ _), 
    rw [←(subset_iff_inter_eq_left.mp hXY), inter_union_parallel_classes],
  end,
  R3 := λ X Y, begin
    dsimp only, 
    convert M.rank_submod _ _, apply union_union_parallel_classes,
    apply inter_union_parallel_classes, 
  end }

lemma si_r (M : matroid α) (S : set M.parallel_class) : 
  M.si.r S = M.r (union_parallel_classes S) := 
rfl 

/- it is more convenient to think of the simplification rank in terms of a fixed transversal of the parallel classes-/
lemma si_r_transversal {M : matroid α} (f : M.transversal) (S : set M.parallel_class) : 
  (si M).r S = M.r (f '' S) := 
by rw [←rank_img_transversal, si_r]

lemma si_is_loopless (M : matroid α) : 
  (si M).is_loopless := 
let f := M.choose_transversal in 
  loopless_iff_all_nonloops.mpr (λ S, by 
  { rw [nonloop_iff_r, si_r_transversal f, image_singleton, ←nonloop_iff_r], apply nonloop_of_range_transversal,  }) 

lemma si_is_simple (M : matroid α) : 
  (si M).is_simple :=
begin
  let f := M.choose_transversal, 
  refine simple_iff_no_loops_or_parallel_pairs.mpr ⟨(M.si_is_loopless), λ P Q hPQ, _⟩,  
  apply eq_of_parallel_range_transversal f, 
  obtain ⟨-,-,hr⟩ := hPQ, 
  refine ⟨_,_,_⟩, all_goals {try {apply nonloop_of_range_transversal}}, 
  rwa [si_r_transversal f, image_pair] at hr, 
end

lemma si_is_irestr (M : matroid α) : 
  (si M).is_irestr_of M :=
begin
  rw irestr_of_iff_exists_map, 
  let f := choose_transversal M, 
  exact ⟨⟨f, transversal_inj f⟩, λ S, by {rw [si_r_transversal f], refl}⟩, 
end

lemma si_is_iminor (M : matroid α) : 
  (si M).is_iminor_of M := 
iminor_of_irestr M.si_is_irestr 

lemma si_r_eq_r_parallel_cl_image (M : matroid α) (X : set α) :
  (si M).r (M.parallel_cl_image_of X) = M.r X :=
by {rw [si_r, ← rank_eq_rank_parallel_cl_image_of]} 

lemma simple_set_of_weak_le {N M : matroid α}{X : set α}(hNM : N ≤ M)(hX : N.is_simple_set X):
  M.is_simple_set X := 
by {rw simple_set_iff_r at hX ⊢, exact λ Y hY hfincard, le_trans (hX Y hY hfincard) (hNM Y)} 

lemma simple_loopify_iff {D : set α} : 
  (N ⟍ D).is_simple_set S ↔ N.is_simple_set S ∧ S ∩ D = ∅ := 
begin
  refine ⟨λ h, ⟨ simple_set_of_weak_le (loopify_is_weak_image _ _) h ,_⟩, λ h, _⟩, 
  { by_contra hn, 
    obtain ⟨e,⟨heS,heD⟩⟩ := ne_empty_iff_has_mem.mp hn, 
    rw [simple_set_iff_no_loops_or_parallel_pairs, loopless_set_iff_all_nonloops] at h, 
    exact loop_iff_not_nonloop.mp (loop_of_loopify N heD) (h.1 e heS)},
  simp_rw [is_simple_set, indep_loopify_iff],
  exact λ X hX hfincard, ⟨h.1 X hX hfincard, disjoint_of_subset_left' hX h.2⟩,  
end

lemma simple_loopify_to_iff {R : set α}: 
  (N ‖ R).is_simple_set S ↔ N.is_simple_set S ∧ S ⊆ R :=
by rw [loopify_to, simple_loopify_iff, subset_iff_disjoint_compl]

end simple 

section simple_minor


/-- If N is loopless and is isomorphic to a minor of a pminor of M, then N is isomorphic 
to a minor of M.  -/
lemma iminor_of_iminor_of_pminor {N : matroid β} {M' M: matroid α} (hN : N.is_loopless)
(hNM' : N.is_iminor_of M') (hM'M : M'.is_pminor_of M) :
N.is_iminor_of M :=
begin
  obtain ⟨φ,C, hrange, hr, hCi, hCr⟩ := iminor_of_iff_exists_good_C.mp hNM', 
  obtain ⟨C',D',hC'D', h⟩ := pminor_iff_exists_pr_lp_disjoint.mp hM'M, substI h, 
  clear hM'M hNM', 
  
  have hrange' : range φ ∩ (C' ∪ D') = ∅, 
  { by_contra hn, 
    obtain ⟨e,he⟩ := ne_empty_iff_has_mem.mp hn, clear hn,
    obtain ⟨heφ, heC⟩ := ((mem_inter_iff _ _ _).mp he), clear he, 
    obtain ⟨f,rfl⟩ := mem_range.mp heφ, clear heφ, 
    specialize hr {f}, 
    --have := @rank_single_of_loopless β _inst_2 N hN f,
    
    rw [rank_single_of_loopless hN, image_singleton] at hr,
    rw [union_comm, rank_eq_rank_union_rank_zero C _, sub_self] at hr, 
    exact one_ne_zero hr, 
    apply rank_zero_of_subset_rank_zero (singleton_subset_iff.mpr heC),
    apply rank_zero_of_pr_lp, },
  have hCC'D' : C ∩ (C' ∪ D') = ∅, 
  
  rw [←fincard_zero_iff_empty, 
        ←rank_zero_of_inter_rank_zero C (rank_zero_of_pr_lp M C' D'),
        ←r_indep (inter_indep_of_indep_left _ (C' ∪ D') hCi)],
  
  refine iminor_of_iff_exists_embedding.mpr ⟨φ, C ∪ C', _, λ X, _⟩, 
  { rw [disjoint_iff_inter_eq_empty] at *, 
    rw disjoint_iff_subset_compl at *, 
    refine subset.trans (subset_inter hrange hrange') _, 
    intros x, 
    simp only [and_imp, compl_union, mem_inter_eq, mem_compl_eq], 
    tauto},
  
  have h' : ∀ Z: set α, Z ∩ (C' ∪ D') = ∅ → D' ∩ Z = ∅, 
  { intros Z hZ, rw inter_comm, apply disjoint_of_subset_right' (subset_union_right C' D') hZ, }, 

  rw [hr X, loopify_rank_of_disjoint (M ⟋ C') (h' _ hCC'D'), ←union_assoc,  
      loopify_rank_of_disjoint (M ⟋ C'), project_r, project_r], ring, 

  rw [inter_distrib_left, h' _ hCC'D', disjoint_of_subset_right' _ (h' _ hrange'), union_self], 
  apply image_subset_range,  
end


/-- a simple matroid is a minor of M iff if it is a minor of si M . -/

lemma iminor_iff_iminor_si {N : matroid β} {M : matroid α} (hN : N.is_simple) :
  N.is_iminor_of (si M) ↔ N.is_iminor_of M :=
begin
  refine ⟨λ h, iminor_trans h M.si_is_iminor, λ h, iminor_of_iff_exists_embedding.mpr _⟩,
  
  obtain ⟨ce⟩ := iminor_of_iff_exists_con_emb.mp h, 
  -- all elements of N map to nonloops of M...
  have hnl : ∀ x, M.is_nonloop (ce.e x), from 
    λ x, ce.nonloop_of_nonloop (nonloop_of_simple hN x), 
  
  -- so we can define a map φ' taking β to nonloops of M 
  set φ' : β → M.nonloop := λ x, ⟨ce.e x, hnl x⟩ with hφ', 

  -- the contract_set is the parallel_cl image of C
  set C' := M.parallel_cl_image_of ce.C with hC', 

  -- the contract map is basically (parallel_class_of) ∘ φ, modulo punctuation 
  refine ⟨⟨λ b, parallel_class_of' (φ' b), λ x y hxy, _⟩, C', _, λ X, _⟩, 
  
  -- the contract map is injective 
  { dsimp only at hxy, 
    simp only [hφ', parallel_class_of'_eq, hφ', subtype.mk_eq_mk, subtype.coe_mk] at hxy, 
    have hr := ce.rank_le_rank_image {x,y}, 
    rw [image_pair, (parallel_of_parallel_cl_eq_left (hnl x) hxy).2.2]  at hr, 
    exact eq_of_rank_le_one_simple hN hr},
  
  -- the contract set is disjoint from the contract map's range 
  { simp only [parallel_class_of'_eq, function.embedding.coe_fn_mk, subtype.coe_mk, 
      ←disjoint_iff_inter_eq_empty, disjoint_left,  forall_apply_eq_imp_iff', mem_range, 
      exists_imp_distrib, hC', mem_parallel_cl_image_of_iff], 
    rintros b ⟨a, ha⟩, 
    rw [mem_inter_iff, mem_parallel_cl] at ha, 
    have hr := ha.2.2.2, 
    have hr' := ce.on_rank {b}, 
    rw [rank_nonloop (nonloop_of_simple hN b), union_comm, image_singleton, union_singleton, 
    rank_eq_rank_parallel_ext ha.1 ha.2] at hr', linarith,}, 

  -- the rank functions agree. A bit nasty 
  convert ce.on_rank X using 2, swap, 
  { rw hC', exact M.si_r_eq_r_parallel_cl_image _, },  
  rw [hC', ← M.si_r_eq_r_parallel_cl_image], 
  convert rfl, 
  ext P, rcases P with ⟨P, hP⟩,  
  simp only [mem_parallel_cl_image_of_iff, mem_image, parallel_class_of'_eq, 
  mem_union_eq, subtype.mk_eq_mk, function.embedding.coe_fn_mk, subtype.coe_mk, 
  nonempty_inter_iff_exists_right], 
  split, 
  { rintro ⟨⟨x,hx⟩, (⟨b, hbX, hbx⟩  | hxc )⟩, 
    { refine or.inl ⟨b, hbX, _⟩,
      rw [hbx, subtype.coe_mk, parallel_class_eq_cl_mem hP hx]},
    exact or.inr ⟨_, hxc⟩,}, 
  rintro (⟨b, ⟨hb, rfl⟩⟩ | ⟨x, hx⟩), 
  { refine ⟨⟨ce.e b,_⟩, or.inl ⟨b,hb,rfl⟩⟩,
    rw [mem_parallel_cl, parallel_refl_iff_nonloop], 
    apply ce.nonloop_of_nonloop (nonloop_of_simple hN _) }, 
  exact ⟨x, or.inr hx⟩, 
end 


end simple_minor 
end matroid 


