
import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax
import .rankfun matroid.submatroid.minor_iso matroid.submatroid.projection 

noncomputable theory 
open_locale classical 

open set 
namespace matroid 

/- 
This file is a mess. This mostly stems from the awkwardness of defining 'parallel'. Should it be defined for all pairs
e,f, or just for pairs of nonloops? Should a parallel class be a set of nonloops, or a set of elements? 

Going with the 'bundled nonloop' approach leads to forever folding and unfolding coercions, although it is nicer that parallel is an 
equivalence relation, as setoid stuff in the API becomes available. 

Going with the unbundled approach leads to constantly passing around is_nonloop proof terms, but the computations are flatter 
and often more pleasant. 

The problem is that loops are there, and so can't be completely ignored, but can still be mostly ignored. The current approach
is unbundled, but I'm not convinced it's the best one. 
-/


variables {α β : Type} [fintype α][fintype β]

/-- equivalence relation of being parallel for nonloops  -/
def parallel_nl (M : matroid α) (e f : nonloop M) : Prop := 
  M.r ({e,f}) = 1 

/-- relation of being both nonloops and having a rank-one union. Irreflexive at loops; 
    an equivalence relation when restricted to nonloops -/
def parallel (M : matroid α) (e f : α) : Prop := 
  M.is_nonloop e ∧ M.is_nonloop f ∧ M.r {e,f} = 1 

--lemma rank_of_parallel {M : matroid α} {e f : α} (h )

lemma rank_eq_rank_of_parallel_ext {M : matroid α} {X Y : set α} (hXY : X ⊆ Y) 
(hY : ∀ y : Y, M.is_nonloop y → ∃ x : X, M.parallel x y) : 
M.r X = M.r Y := 
begin
  refine rank_eq_of_rank_all_insert_eq hXY (λ y, _), 
  rcases M.loop_or_nonloop y with (hy | hy), rw rank_eq_rank_insert_loop _ hy,  
  obtain ⟨⟨x,hx⟩, ⟨hxnl,hznl,hr⟩⟩ := hY y hy, 
  dsimp only [subtype.coe_mk] at *, rw nonloop_iff_r at *, 
  have hr' := rank_eq_of_union_eq_rank_subset X (singleton_subset_pair_left x y) (by rw [hr, hxnl]), 
  rw [subset_iff_union_eq_left.mp (singleton_subset_iff.mpr hx)] at hr', 
  rw [hr', eq_comm, union_comm], 
  apply rank_eq_of_union_eq_rank_subset, 
    apply singleton_subset_pair_right, 
  rw [hznl, hr],   
end


lemma parallel_nl_of_parallel {M : matroid α} {e f : α} (h : M.parallel e f ) :
  ∃ (he : M.is_nonloop e) (hf : M.is_nonloop f), M.parallel_nl ⟨e,he⟩ ⟨f,hf⟩ :=
⟨h.1,h.2.1,h.2.2⟩

lemma parallel_of_parallel_nl {M : matroid α} {e f : M.nonloop} (h : M.parallel_nl e f) : 
  M.parallel e.1 f.1 :=
⟨e.2,f.2,h⟩

lemma parallel_iff_parallel_nl {M : matroid α} {e f : α} :
  M.parallel e f ↔ ∃ (he : M.is_nonloop e) (hf : M.is_nonloop f), M.parallel_nl ⟨e,he⟩ ⟨f,hf⟩:= 
by tidy

/-- parallel_nl in dual -/
def series (M : matroid α) (e f : nonloop (dual M)) : Prop := 
  (dual M).parallel_nl e f 

lemma parallel_nl_refl (M : matroid α) : 
  reflexive M.parallel_nl:= 
λ e, by {unfold parallel_nl, rw pair_eq_singleton, exact e.property}

lemma parallel_nl_symm (M : matroid α) : 
  symmetric M.parallel_nl:= 
λ x y, by {simp_rw [parallel_nl, pair_comm], tauto,}

lemma parallel_nl_iff_dep {M: matroid α} {e f : nonloop M} : 
  M.parallel_nl e f ↔ (e = f ∨ M.is_dep {e,f}) :=
begin
  unfold parallel_nl, rw dep_iff_r,  refine ⟨λ h, ((or_iff_not_imp_left.mpr (λ hne, _))), λ h, _ ⟩,
  have := size_pair (λ h', hne (subtype.ext h')) , 
  rw h, unfold_coes at *, linarith,  
  cases h, rw [h, pair_eq_singleton], exact f.property, 
  have := rank_two_nonloops_lb e f, 
  have := size_pair_ub e.1 f.1,
  unfold_coes at *, rw ←int.le_sub_one_iff at h, linarith, 
end


lemma parallel_nl_iff_cct {M: matroid α} {e f : nonloop M} : 
  M.parallel_nl e f ↔ (e = f ∨ M.is_circuit {e,f}) :=
begin
  refine ⟨λ h, _, λ h, (parallel_nl_iff_dep.mpr (or.imp_right _ h : (e = f) ∨ is_dep M ({e,f})))⟩, 
  replace h := parallel_nl_iff_dep.mp h, cases h, exact or.inl h, apply or_iff_not_imp_left.mpr, intro h', 
  refine ⟨h,λ Y hY, _⟩, rcases ssubset_pair hY, 
  rw h_1, exact empty_indep M,  unfold_coes at h_1,  cases h_1; 
  {rw h_1, apply coe_nonloop_indep,},
  apply circuit_dep, 
end

lemma parallel_nl_trans (M : matroid α) :
  transitive M.parallel_nl :=
begin
  intros e f g hef hfg, unfold parallel_nl at *, 
  have := M.rank_submod ({e,f}) ({f,g}), rw [hef, hfg] at this, 
  have h1 : 1 ≤ M.r (({e,f}) ∩ ({f,g})),  
  {rw ←rank_coe_nonloop f, refine M.rank_mono (subset_inter _ _ ); simp, },
  have h2 := M.rank_mono (_ : ({e,g} : set α)  ⊆ {e,f} ∪ {f,g}), swap, 
  {intro x, simp, tauto,  }, 
  linarith [(rank_two_nonloops_lb e g)],  
end

lemma parallel_refl_nonloop {M : matroid α} {e : α} (h : M.is_nonloop e) : 
  M.parallel e e :=
⟨h,h,by rwa [pair_eq_singleton]⟩


lemma parallel_iff_dep {M : matroid α} {e f : α} (he : M.is_nonloop e) (hf : M.is_nonloop f) :
  M.parallel e f ↔ (e = f) ∨ M.is_dep {e,f} :=
begin
  split, 
  { rintros ⟨-,-,hef⟩, 
    by_contra hn, push_neg at hn, cases hn with hne hef',  
    rw [←indep_iff_not_dep, indep_iff_r, hef, size_pair hne] at hef',
    norm_num at hef', },
  rintros (heq | hef), rw heq, exact parallel_refl_nonloop hf,
  rw [dep_iff_r, ←int.le_sub_one_iff] at hef, 
  refine ⟨he,hf,_⟩,  
  linarith [nonloop_iff_r.mp he, M.rank_mono (by tidy: {e} ⊆ {e,f}), size_pair_ub e f],   
end

lemma parallel_iff_cct {M: matroid α} {e f : α} (he : M.is_nonloop e) (hf : M.is_nonloop f) : 
  M.parallel e f ↔ (e = f ∨ M.is_circuit {e,f}) :=
begin
  rw parallel_iff_dep he hf, split, 
  { rintros (heq | hdep), left, assumption, right, 
    rw circuit_iff_i, 
    refine ⟨dep_iff_not_indep.mp hdep, λ Y hY, _⟩, 
    rcases ssubset_pair hY with (rfl | rfl | rfl), apply M.empty_indep, 
    all_goals {rwa ←nonloop_iff_indep}, },
  rintros (heq | hef), left, assumption, right, 
  apply circuit_dep hef,  
end

lemma parallel_of_nonloop_dep {M : matroid α} {e f : α} (he : M.is_nonloop e) (hf : M.is_nonloop f) (h : M.is_dep {e,f}) :
  M.parallel e f := 
by {rw parallel_iff_dep he hf,right, assumption,  }

lemma parallel_of_circuit {M : matroid α} {e f : α} (hef : e ≠ f) (h : M.is_circuit {e,f}) :
  M.parallel e f := 
begin
  rw parallel_iff_cct, right, assumption, all_goals
  { rw [nonloop_iff_not_loop, loop_iff_circuit], by_contra hn, 
    apply circuit_not_ssubset_circuit hn h,},
  apply singleton_ssubset_pair_left hef, 
  apply singleton_ssubset_pair_right hef,    
end


lemma parallel_trans (M : matroid α) : 
  transitive M.parallel :=
begin
  rintros e f g ⟨he,hf,hef⟩ ⟨-,hg,hfg⟩,-- unfold parallel at *, 
  refine ⟨he,hg,_⟩, 
  have hef' : M.parallel_nl ⟨e,he⟩ ⟨f,hf⟩:= hef, 
  have hfg' : M.parallel_nl ⟨f,hf⟩ ⟨g,hg⟩ := hfg, 
  exact parallel_nl_trans M hef' hfg', 
end

lemma parallel_symm (M : matroid α) : 
  symmetric M.parallel :=
by {rintros e f ⟨he,hf,hef⟩, refine ⟨hf,he,_⟩, rwa pair_comm}

@[symm] lemma parallel_symm' {M : matroid α} {e f : α} (hef : M.parallel e f) :
  M.parallel f e := 
parallel_symm M hef

lemma parallel_comm {M : matroid α} {e f : α} :
  M.parallel e f ↔ M.parallel f e :=
⟨λ h, by {symmetry, exact h}, λ h, by {symmetry, exact h}⟩

@[trans] lemma parallel_trans' {M : matroid α} {e f g : α} (hef : M.parallel e f) (hfg : M.parallel f g) : 
  M.parallel e g := 
parallel_trans M hef hfg

lemma parallel_nl_is_equivalence (M : matroid α) : 
  equivalence M.parallel_nl := 
  ⟨M.parallel_nl_refl, M.parallel_nl_symm, M.parallel_nl_trans⟩

lemma series_is_equivalence (M : matroid α) : 
  equivalence M.series :=
parallel_nl_is_equivalence M.dual 

/-- the parallel class containing e. Empty if e is a loop -/
def parallel_cl (M : matroid α) (e : α) : set α := 
  {a : α | M.parallel a e}
  
lemma parallel_cl_loop_empty {M : matroid α} {e : α} (he : M.is_loop e) : 
  M.parallel_cl e = ∅ := 
by {ext, simp [parallel_cl, parallel, loop_iff_not_nonloop.mp he]}


lemma parallel_cl_nonempty_of_nonloop {M : matroid α} {e : α} (he : M.is_nonloop e) : 
  (M.parallel_cl e).nonempty := 
⟨e, by {rw [parallel_cl, mem_set_of_eq], exact parallel_refl_nonloop he,  }⟩ 

lemma mem_parallel_cl {M : matroid α} {e f : α} : 
  e ∈ M.parallel_cl f ↔ M.parallel e f := 
by simp_rw [parallel_cl, mem_set_of_eq]
  

lemma parallel_cl_eq_empty_iff_loop {M : matroid α} {e : α} :
  M.parallel_cl e = ∅ ↔ M.is_loop e :=
begin
  refine ⟨λ h, by_contra (λ hn, _), λ h, parallel_cl_loop_empty h⟩, 
  rw ← nonloop_iff_not_loop at hn, 
  rw empty_iff_has_no_mem at h, 
  apply h e, 
  rw mem_parallel_cl, 
  apply parallel_refl_nonloop hn, 
end

def is_parallel_class (M : matroid α) (P : set α)  := 
  ∃ e,  M.is_nonloop e ∧ P = M.parallel_cl e 

def parallel_class (M : matroid α) : Type := {X : set α // M.is_parallel_class X}

/-- function taking a nonloop to its parallel class -/
def parallel_cl' {M : matroid α} (e : M.nonloop) : M.parallel_class := 
  ⟨M.parallel_cl e, ⟨e,⟨e.property, rfl⟩⟩⟩ 

lemma parallel_cl_eq_of_parallel {M : matroid α} {e f : α} (hef : M.parallel e f) :
   M.parallel_cl e = M.parallel_cl f :=
begin
  ext, rw [mem_parallel_cl, mem_parallel_cl], 
  have := parallel_symm' hef,
  split; {intro, transitivity; assumption,},
end

lemma parallel_of_parallel_cl_eq_left {M : matroid α} {e f : α} (he : M.is_nonloop e)
(hef : M.parallel_cl e = M.parallel_cl f) : 
  M.parallel e f :=
by {rw [← mem_parallel_cl, ← hef, mem_parallel_cl], apply parallel_refl_nonloop he}

lemma parallel_iff_parallel_cl'_eq {M : matroid α} {e f : M.nonloop} : 
  M.parallel e f ↔ parallel_cl' e = parallel_cl' f  :=
begin
  simp_rw [parallel_cl', parallel_cl, subtype.mk_eq_mk, ext_iff, mem_set_of_eq],  
  refine ⟨λ h x, (have h' : _ := parallel_symm M h, ⟨λ hxe, _, λ hxf, _⟩), λ h, _⟩, 
  repeat {transitivity, assumption, assumption, }, 
  { apply (h e).mp, apply parallel_refl_nonloop e.property}, 
end


instance coe_parallel_class_to_set {M : matroid α} : has_coe (M.parallel_class) (set α) := ⟨subtype.val⟩ 
instance parallel_class_fintype {M : matroid α} : fintype M.parallel_class := 
by {unfold parallel_class, apply_instance} 

lemma parallel_of_mems_parallel_class {M : matroid α} {P : M.parallel_class} {e f : α}
(he : e ∈ (P : set α)) (hf : f ∈ (P : set α)) : 
M.parallel e f := 
begin
  cases P with P hP, 
  obtain ⟨x, ⟨hx, rfl⟩⟩ := hP, 
  rw [subtype.coe_mk, mem_parallel_cl] at he hf, 
  transitivity, assumption, symmetry, assumption, 
end


lemma nonloop_of_mem_parallel_class {M : matroid α} {P : set α} {e : α} (heP : e ∈ P) (h : M.is_parallel_class P) :
  M.is_nonloop e := 
by {rcases h with ⟨f, ⟨hf,rfl⟩⟩, rw mem_parallel_cl at heP, exact heP.1} 

lemma parallel_cl_eq_cl_minus_loops (M : matroid α) (e : α) : 
  M.parallel_cl e = M.cl {e} \ M.loops :=
begin
  by_cases he: M.is_nonloop e, swap, 
  { ext x, rw [mem_diff, mem_parallel_cl],
    refine ⟨λ h, false.elim (he h.2.1), λ h, false.elim _⟩,
    rw [←loop_iff_not_nonloop, loop_iff_r] at he, 
    rw [mem_cl_iff_r,he, ←nonloop_iff_not_mem_loops, nonloop_iff_r] at h,
    linarith[h.1, h.2, M.rank_mono_union_right {e} {x}], },
  ext x, 
  simp only [mem_diff, mem_set_of_eq, mem_cl_iff_r, rank_nonloop he, union_singleton, ←nonloop_iff_not_mem_loops], 
  split, { rintros ⟨hx,he,hxe⟩, split; assumption,  }, 
  rintros ⟨hxe,hx⟩, exact ⟨hx,he,hxe⟩, 
end

lemma rank_parallel_cl {M : matroid α} {e : α} (he : M.is_nonloop e) : 
  M.r (M.parallel_cl e) = 1 := 
by rwa [parallel_cl_eq_cl_minus_loops, rank_eq_rank_diff_rank_zero _ M.rank_loops, rank_cl, ←nonloop_iff_r]

lemma parallel_class_eq_cl_nonloop_diff_loops {M : matroid α} {P : set α} : 
  M.is_parallel_class P ↔ P.nonempty ∧ (∀ e ∈ P, P = M.cl {e} \ M.loops ) := 
begin
  simp_rw [←parallel_cl_eq_cl_minus_loops, is_parallel_class],  
  split,
  { rintros ⟨e,he,rfl⟩, refine ⟨⟨e,_⟩, _⟩, apply parallel_refl_nonloop, assumption, 
    intros f hf, ext x, simp only [mem_parallel_cl] at *, have := parallel_symm' hf, 
    split; {intro h, transitivity; assumption}, },
  rintros ⟨⟨e,he⟩,hP⟩, 
  specialize hP e he, rw [hP, mem_parallel_cl] at he, 
  exact ⟨e, he.1, hP⟩, 
end

/-- the natural equivalence between points and parallel classes in a matroid -/
def parallel_class_point_equiv {M : matroid α} : 
  M.parallel_class ≃ M.point := 
{ to_fun := λ P, ⟨P.val ∪ M.loops, 
  let ⟨e,he,h⟩ := P.property in by 
  { simp_rw [h, point_iff_cl_nonloop, parallel_cl_eq_cl_minus_loops, diff_union_self, union_comm, 
    subset_iff_union_eq_left.mp (M.loops_subset_cl {e})],
    exact ⟨e,he,rfl⟩, }⟩, 
inv_fun := λ P, ⟨P.val \ M.loops, 
  let ⟨e,he,hP⟩ := point_iff_cl_nonloop.mp P.2 in by 
  { rw [hP, ← parallel_cl_eq_cl_minus_loops], 
    refine ⟨e, he, rfl⟩,}⟩,
left_inv := λ P, let ⟨e,he,h⟩ := P.2 in by 
  { simp_rw [h, union_diff_right, parallel_cl_eq_cl_minus_loops, diff_diff, union_self, 
    ← parallel_cl_eq_cl_minus_loops, ← h], simp, },
right_inv := λ P, let ⟨e,he,hP⟩ := point_iff_cl_nonloop.mp P.2 in by 
  { dsimp only, simp_rw [hP, diff_union_self, union_comm, 
    subset_iff_union_eq_left.mp (M.loops_subset_cl {e}), ←hP],simp, }}


lemma parallel_class_nonempty {M : matroid α} (P : M.parallel_class) :
  set.nonempty (P : set α) := 
(parallel_class_eq_cl_nonloop_diff_loops.mp P.property).1


lemma nonloop_of_parallel_cl_is_parallel_class {M : matroid α} {e : α} {P : M.parallel_class} (h : (P : set α) = (M.parallel_cl e)) : 
  M.is_nonloop e := 
begin
  by_contra hn, 
  rw parallel_cl_loop_empty (loop_iff_not_nonloop.mpr hn) at h, 
  exact nonempty.ne_empty (parallel_class_nonempty P) h, 
end

lemma parallel_class_eq_parallel_cl_of_mem {M : matroid α} {P : M.parallel_class} {e : α} (he : e ∈ (P : set α)) :
  (P : set α) = M.parallel_cl e := 
begin
  obtain ⟨-, h'⟩ := parallel_class_eq_cl_nonloop_diff_loops.mp P.property, 
  simp_rw [←parallel_cl_eq_cl_minus_loops, subtype.val_eq_coe] at h', 
  rwa ←(h' e he), 
end 

lemma parallel_class_is_cl_diff_loops {M : matroid α} (P : M.parallel_class) : 
  ∃ e ∈ (P : set α), M.is_nonloop e ∧ (P : set α) = M.cl {e} \ M.loops :=
begin
  rcases parallel_class_eq_cl_nonloop_diff_loops.mp P.property with ⟨⟨e,he⟩,hP⟩, 
  exact ⟨e,he,nonloop_of_mem_parallel_class he P.property, hP e he⟩, 
end

lemma parallel_class_is_parallel_cl_nonloop {M : matroid α} (P : M.parallel_class) :
  ∃ e ∈ (P : set α), M.is_nonloop e ∧ (P : set α) = M.parallel_cl e :=
by {have := parallel_class_is_cl_diff_loops P, simp_rw ←parallel_cl_eq_cl_minus_loops at this, assumption}

lemma parallel_class_is_parallel_cl {M : matroid α} (P : M.parallel_class) :
  ∃ e, (P : set α) = M.parallel_cl e :=
by {obtain ⟨e,he,he'⟩ := parallel_class_is_parallel_cl_nonloop P, use ⟨e,he'.2⟩,   }

lemma mem_parallel_class_iff_parallel_cl {M : matroid α} {e : α} {P : M.parallel_class} : 
  e ∈ (P : set α) ↔ (P : set α) = M.parallel_cl e :=
begin
  refine ⟨λ h, parallel_class_eq_parallel_cl_of_mem h, λ h, _⟩, 
  rw [h, parallel_cl, mem_set_of_eq], 
  exact parallel_refl_nonloop (nonloop_of_parallel_cl_is_parallel_class h),
end 

lemma rank_parallel_class (M : matroid α) (P : M.parallel_class ) : 
  M.r P = 1 := 
by {obtain ⟨e,heP,he, hP⟩ := parallel_class_is_parallel_cl_nonloop P, rw hP, apply rank_parallel_cl he}

lemma parallel_class_eq_of_nonempty_inter {M : matroid α} {P₁ P₂ : M.parallel_class} (h : set.nonempty (P₁ ∩ P₂ : set α)) : 
  P₁ = P₂ :=
begin
  rcases h with ⟨x,hx⟩, 
  rcases parallel_class_is_parallel_cl_nonloop P₁ with ⟨e₁,he₁P,⟨he₁,h₁⟩⟩,  
  rcases parallel_class_is_parallel_cl_nonloop P₂ with ⟨e₂,he₂P,⟨he₂,h₂⟩⟩,  
  
  rw [mem_inter_iff, h₁,h₂] at hx, 
  have h₁₂ : M.parallel e₁ e₂, {transitivity x, symmetry, exact hx.1, exact hx.2},
  have h₂₁ := parallel_symm' h₁₂, 
  rcases P₁ with ⟨P₁, hP₁⟩, rcases P₂ with ⟨P₂, hP₂⟩, rw subtype.mk_eq_mk, 
  rw subtype.coe_mk at *, subst h₁, subst h₂, 
  ext y, simp only [mem_parallel_cl],
  split; {intro h, symmetry, transitivity, assumption, symmetry, assumption,}, 
end

lemma disj_of_distinct_parallel_classes {M : matroid α} {P₁ P₂ : M.parallel_class} (h : P₁ ≠ P₂) :
  disjoint (P₁ : set α) (P₂ : set α) := 
begin
  by_contra hn, rcases not_disjoint_iff.mp hn with ⟨e,⟨h₁,h₂⟩⟩, 
  exact h (parallel_class_eq_of_nonempty_inter ⟨e,mem_inter h₁ h₂⟩),
end

lemma parallel_class_eq_of_mem_both {M : matroid α} {P₁ P₂ : M.parallel_class} {x : α}
  (h₁ : x ∈ (P₁ : set α)) (h₂ : x ∈ (P₂ : set α)) : 
  P₁ = P₂ := 
parallel_class_eq_of_nonempty_inter ⟨x,mem_inter h₁ h₂⟩

/-- the set of parallel classes of M -/
def parallel_classes_set (M : matroid α) : set (set α) := 
  range (coe : M.parallel_class → set α)

lemma parallel_class_set_disjoint (M : matroid α) : 
  pairwise_disjoint M.parallel_classes_set :=
begin
  rintros S hS T hT hST, 
  rcases mem_range.mp hS with ⟨P₁,rfl⟩, 
  rcases mem_range.mp hT with ⟨P₂,rfl⟩,
  have h : P₁ ≠ P₂ := λ hP₁P₂, by {rw hP₁P₂ at hST, tauto, },
  apply disj_of_distinct_parallel_classes h, 
end

/-- the union of a set of parallel classes of M -/
def union_parallel_classes {M : matroid α} (S : set M.parallel_class) : set α := 
  ⋃₀ (coe '' S)

lemma mem_union_parallel_classes {M : matroid α} {S : set M.parallel_class} {e : α} : 
  e ∈ union_parallel_classes S ↔ ∃ (he : M.is_nonloop e), (parallel_cl' ⟨e,he⟩) ∈ S  := 
begin
  simp_rw [union_parallel_classes, mem_sUnion], split, 
  { rintros ⟨X, hX, heX⟩, 
    obtain ⟨P,hP₁,rfl⟩ := (mem_image _ _ _).mp hX,
    use nonloop_of_mem_parallel_class heX P.property, convert hP₁,  
    unfold parallel_cl', simp only [subtype.coe_mk], 
    cases P, simp only [subtype.mk_eq_mk],  
    rw ←(parallel_class_eq_parallel_cl_of_mem heX), simp},
  rintros ⟨he, heP⟩, 
  refine ⟨M.parallel_cl e, _,_⟩, 
  { simp only [mem_image], exact ⟨_, heP,by simp [parallel_cl']⟩}, 
  simp [parallel_cl, mem_set_of_eq, parallel_refl_nonloop he], 
end

lemma union_union_parallel_classes {M : matroid α} (S₁ S₂ : set M.parallel_class) : 
  union_parallel_classes (S₁ ∪ S₂) = union_parallel_classes S₁ ∪ union_parallel_classes S₂ :=
by simp_rw [union_parallel_classes, image_union, sUnion_union]


lemma inter_union_parallel_classes {M : matroid α} (S₁ S₂ : set M.parallel_class) : 
  union_parallel_classes (S₁ ∩ S₂) = union_parallel_classes S₁ ∩ union_parallel_classes S₂ :=
begin
  simp_rw [union_parallel_classes, ←image_inter (subtype.coe_injective)], 
  apply pairwise_disjoint_inter_sUnion (parallel_class_set_disjoint M); 
  apply image_subset_range, 
end



--lemma intersecting_parallel_nl_classes_eq {M : matroid α} (S : set M.parallel_nl_class) : set α :=

/- property that a map sends parallel classes to representatives -/
def is_transversal {M : matroid α} (f : M.parallel_class → α) :=
  ∀ P, M.parallel_cl (f P) = (P : set α)

def transversal (M : matroid α) := 
  { f : M.parallel_class → α // is_transversal f}

instance coe_transversal {M : matroid α} : has_coe_to_fun M.transversal := { F := _, coe := subtype.val }

lemma transversal_def {M : matroid α} (f : M.transversal) (P : M.parallel_class) : 
  M.parallel_cl (f P) = (P : set α) := 
(f.property P)

lemma transversal_def' {M : matroid α} (f : M.transversal){P : set α} (hP : M.is_parallel_class P) :
  M.parallel_cl (f ⟨P,hP⟩) = P := 
f.property ⟨P,hP⟩ 

lemma nonloop_of_range_transversal {M : matroid α} (f : M.transversal) (P : M.parallel_class) : 
  M.is_nonloop (f P) := 
nonloop_of_parallel_cl_is_parallel_class (f.property P).symm

lemma exists_transversal (M : matroid α) : 
  ∃ (f : M.parallel_class → α), is_transversal f := 
⟨λ P, (classical.some (parallel_class_is_parallel_cl P)), 
 λ P, (classical.some_spec (parallel_class_is_parallel_cl P)).symm ⟩ 

def choose_transversal (M : matroid α) : M.transversal  :=
classical.indefinite_description _ (M.exists_transversal)

lemma transversal_subset_union {M : matroid α} (f : M.transversal) (S : set M.parallel_class) :
  f '' S ⊆ union_parallel_classes S :=
begin
  intros x hx, 
  obtain ⟨P, hP, rfl⟩ := (mem_image _ _ _).mp hx, 
  rw mem_union_parallel_classes, 
  refine ⟨nonloop_of_range_transversal f _,_⟩, 

  simp_rw [parallel_cl', subtype.coe_mk, transversal_def f P], 
  convert hP, cases P, simp, 
end 


lemma eq_of_parallel_range_transversal {M : matroid α} {P Q : M.parallel_class} (f : M.transversal)
(h : M.parallel (f P) (f Q)) : 
  P = Q :=
begin
  cases P with P hP, cases Q with Q hQ, 
  rw [subtype.mk_eq_mk, ←transversal_def' f hP, ←transversal_def' f hQ],  
  have := parallel_symm' h, 
  ext, simp_rw mem_parallel_cl, 
  split; {intro h', transitivity, assumption, assumption,}, 
end

lemma transversal_inj {M : matroid α} (f : M.transversal) :
  function.injective f := 
begin
  intros P Q hPQ, 
  apply eq_of_parallel_range_transversal f, rw hPQ, 
  apply parallel_refl_nonloop (nonloop_of_range_transversal _ _),  
end


lemma size_img_transversal {M : matroid α} (f : M.transversal)
(S : set M.parallel_class) :
  size (f '' S) = size S := 
size_img_inj (transversal_inj f) S

lemma rank_img_transversal {M : matroid α} (f : M.transversal)
(S : set M.parallel_class) :
  M.r (union_parallel_classes S) = M.r (f '' S) :=
begin
  refine (rank_eq_rank_of_parallel_ext (transversal_subset_union f _) (λ y hy, _)).symm, 
  rcases y with ⟨y,hy'⟩, 
  rcases mem_union_parallel_classes.mp hy' with ⟨hy_nl,hP⟩, 
  set PY := parallel_cl' ⟨y,hy_nl⟩ with hPY, 
  refine ⟨ ⟨f PY, _ ⟩, _⟩, apply mem_image_of_mem _ hP, 
  simp_rw [subtype.coe_mk, parallel_comm, ←mem_parallel_cl, transversal_def f PY, hPY, parallel_cl', subtype.coe_mk, mem_parallel_cl],
  apply parallel_refl_nonloop hy_nl,   
end

end matroid 