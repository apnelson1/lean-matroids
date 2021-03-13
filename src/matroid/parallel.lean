
import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax prelim.presetoid
import .rankfun matroid.submatroid.minor_iso

noncomputable theory 
open_locale classical 

universes u v w

open set 
namespace matroid 


variables {α : Type*} {β : Type*} [fintype α] [fintype β]
{M : matroid α} {e f : α} {X Y P : set α}

/-- relation of being both nonloops and having a rank-one union. Irreflexive at loops; 
    an equivalence relation when restricted to nonloops -/
def parallel (M : matroid α) (e f : α) : Prop := 
  M.is_nonloop e ∧ M.is_nonloop f ∧ M.r {e,f} = 1 

lemma parallel_of_rank_le_one 
(he : M.is_nonloop e) (hf : M.is_nonloop f) (hef : M.r {e,f} ≤ 1) :
  M.parallel e f :=
begin
  refine ⟨he, hf, _⟩, 
  rw [← rank_nonloop he, eq_comm], 
  apply rank_eq_of_le_supset,
    apply singleton_subset_pair_left, 
  convert hef, 
end 

lemma rank_parallel_pair (hef : M.parallel e f) : 
  M.r {e,f} = 1 := 
hef.2.2 

lemma rank_one_of_mem_parallel_pair (hef : M.parallel e f) :
  M.r {e} = 1 :=
rank_nonloop hef.1 

lemma rank_eq_rank_parallel_ext (he : e ∈ X) (hef : M.parallel e f) : 
  M.r (insert f X) = M.r X :=
begin
  convert (rank_eq_of_union_eq_rank_subset X 
    (singleton_subset_pair_left e f)
    (by rw [rank_parallel_pair hef, rank_one_of_mem_parallel_pair hef])).symm, 
  { rw [pair_comm, pair_eq_union, union_assoc, ← union_singleton, union_comm], 
    convert rfl, 
    rw [union_comm, union_singleton, insert_eq_of_mem he], },
  rw [union_comm, union_singleton, insert_eq_of_mem he],
end

lemma rank_eq_rank_of_parallel_ext (hXY : X ⊆ Y) 
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

lemma parallel_refl_of_nonloop (h : M.is_nonloop e) : 
  M.parallel e e :=
⟨h,h,by rwa [pair_eq_singleton]⟩

lemma parallel_refl_of_parallel (h : M.parallel e f) : 
  M.parallel e e :=
parallel_refl_of_nonloop h.1 

lemma parallel_irrefl_of_loop (h : M.is_loop e) : 
  ¬M.parallel e e := 
λ h', (loop_iff_not_nonloop.mp h) h'.1 

lemma parallel_refl_iff_nonloop :
  M.parallel e e ↔ M.is_nonloop e :=
⟨λ h, nonloop_iff_not_loop.mpr 
  (λ hl, (parallel_irrefl_of_loop hl) h), 
  λ h, parallel_refl_of_nonloop h⟩ 

lemma parallel_irrefl_iff_loop :
  ¬M.parallel e e ↔ M.is_loop e :=
by rw [loop_iff_not_nonloop, not_iff_not, parallel_refl_iff_nonloop]

lemma parallel_iff_dep (he : M.is_nonloop e) (hf : M.is_nonloop f) :
  M.parallel e f ↔ (e = f) ∨ M.is_dep {e,f} :=
begin
  split, 
  { rintros ⟨-,-,hef⟩, 
    by_contra hn, push_neg at hn, cases hn with hne hef',  
    rw [←indep_iff_not_dep, indep_iff_r, hef, size_pair hne] at hef',
    norm_num at hef', },
  rintros (heq | hef), rw heq, exact parallel_refl_of_nonloop hf,
  rw [dep_iff_r, ←int.le_sub_one_iff] at hef, 
  refine ⟨he,hf,_⟩,  
  linarith [nonloop_iff_r.mp he, M.rank_mono (by tidy: {e} ⊆ {e,f}), size_pair_ub e f],   
end

lemma parallel_iff_cct {M: matroid α} (he : M.is_nonloop e) (hf : M.is_nonloop f) : 
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

lemma parallel_of_nonloop_dep 
(he : M.is_nonloop e) (hf : M.is_nonloop f) (h : M.is_dep {e,f}) :
  M.parallel e f := 
by {rw parallel_iff_dep he hf,right, assumption,  }

lemma parallel_of_circuit (hef : e ≠ f) (h : M.is_circuit {e,f}) :
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
  rintros e f g ⟨he,hf,hef⟩ ⟨-,hg,hfg⟩, 
  have := M.rank_submod ({e,f}) ({f,g}), 
  rw [hef, hfg] at this, 
  have h1 : 1 ≤ M.r (({e,f}) ∩ ({f,g})),  
  {rw ←rank_nonloop hf, refine M.rank_mono (subset_inter _ _ ); simp, },
  have h2 := M.rank_mono (_ : ({e,g} : set α)  ⊆ {e,f} ∪ {f,g}), swap, 
  { intro x, simp, tauto,  }, 
  apply parallel_of_rank_le_one he hg, 
  linarith, 
end

lemma parallel_symm (M : matroid α) : 
  symmetric M.parallel :=
by {rintros e f ⟨he,hf,hef⟩, refine ⟨hf,he,_⟩, rwa pair_comm}

/-- the presetoid given by α and the parallel relation. Equivalence classes are the 
parallel classes of M, and the kernel is the set of loops of M -/
def ps (M : matroid α) : presetoid α :=
⟨M.parallel, M.parallel_trans, M.parallel_symm ⟩ 

lemma ps_rel_eq_parallel : 
  M.ps.rel = M.parallel := 
rfl 

lemma ps_kernel_eq_loops (M : matroid α) : 
  M.ps.kernel = M.loops :=
by {ext, rw [presetoid.mem_kernel_iff, ← loop_iff_mem_loops, ← parallel_irrefl_iff_loop], refl}


@[symm] lemma parallel_symm' (hef : M.parallel e f) :
  M.parallel f e := 
M.ps.symm hef 

lemma parallel_comm :
  M.parallel e f ↔ M.parallel f e :=
M.ps.rel_comm 

@[trans] lemma parallel_trans' {e f g : α} (hef : M.parallel e f) (hfg : M.parallel f g) : 
  M.parallel e g := 
M.ps.trans hef hfg

/-- the parallel class containing e. Empty if e is a loop -/
def parallel_cl (M : matroid α) (e : α) : set α := 
  M.ps.cl e 
  
lemma parallel_cl_loop_empty (he : M.is_loop e) : 
  M.parallel_cl e = ∅ := 
by {rw [parallel_cl, presetoid.cl_eq_empty_iff], rwa ← parallel_irrefl_iff_loop at he }

lemma mem_parallel_cl : 
  e ∈ M.parallel_cl f ↔ M.parallel e f := 
M.ps.mem_cl_iff

lemma parallel_cl_nonempty_of_nonloop (he : M.is_nonloop e) : 
  (M.parallel_cl e).nonempty := 
⟨e, by rwa [mem_parallel_cl, parallel_refl_iff_nonloop]⟩ 

lemma parallel_cl_eq_empty_iff_loop :
  M.parallel_cl e = ∅ ↔ M.is_loop e :=
by {rw [parallel_cl, presetoid.cl_eq_empty_iff, ← parallel_irrefl_iff_loop], refl} 

lemma parallel_cl_nonempty_iff_nonloop : 
  (M.parallel_cl e).nonempty ↔ M.is_nonloop e:= 
⟨ λ h, by {rw [parallel_cl, M.ps.cl_nonempty_iff] at h, rwa ← parallel_refl_iff_nonloop, }, 
  λ h, parallel_cl_nonempty_of_nonloop h⟩ 

def is_parallel_class (M : matroid α) (P : set α)  := 
  M.ps.is_class P  

lemma parallel_class_iff_is_parallel_cl :
  M.is_parallel_class P ↔ (∃ a, M.is_nonloop a ∧ P = M.parallel_cl a) :=
by {simp_rw [is_parallel_class, M.ps.is_class_iff_rep, ← parallel_refl_iff_nonloop], refl} 

lemma rep_parallel_class (hP : M.is_parallel_class P) :
  (∃ a, M.is_nonloop a ∧ P = M.parallel_cl a) := 
by rwa ← parallel_class_iff_is_parallel_cl

lemma parallel_cl_is_parallel_class (he : M.is_nonloop e) :
  M.is_parallel_class (M.parallel_cl e) :=
M.ps.cl_is_class (parallel_refl_iff_nonloop.mpr he)


/-- the property that X ⊆ Y, up to parallel -/
def parallel_covered (M : matroid α) (X Y : set α) :=
  ∀ x ∈ X, M.is_nonloop x → ∃ y ∈ Y, M.parallel x y 

lemma parallel_covered_apply (hXY : M.parallel_covered X Y) (heX : e ∈ X) (he : M.is_nonloop e) :
  ∃ y ∈ Y, M.parallel e y := 
hXY e heX he 

lemma rank_le_rank_of_parallel_covered (h : M.parallel_covered X Y) :
  M.r X ≤ M.r Y := 
begin
  by_contra hn, push_neg at hn, 
  obtain ⟨e, heX, henl, hr⟩ := rank_augment_nonloop hn, 
  obtain ⟨f, hfY, hef⟩ := parallel_covered_apply h heX henl, 
  have h':= rank_eq_rank_parallel_ext hfY (parallel_symm' hef), 
  rw [union_singleton, h'] at hr, 
  exact lt_irrefl _ hr, 
end

lemma rank_eq_rank_of_parallel_covered (h₁ : M.parallel_covered X Y) (h₂ : M.parallel_covered Y X) :
  M.r X = M.r Y :=
by {apply le_antisymm; exact rank_le_rank_of_parallel_covered (by assumption), }


def parallel_class (M : matroid α) := {X : set α // M.is_parallel_class X}

def parallel_class_of (e : α) (he : M.is_nonloop e) : M.parallel_class := 
⟨M.parallel_cl e, parallel_class_iff_is_parallel_cl.mpr ⟨e,he,rfl⟩⟩ 

def parallel_class_of' (e : M.nonloop) : M.parallel_class :=
  parallel_class_of e.1 e.2

@[simp] lemma parallel_class_of'_eq (e : M.nonloop) : 
  parallel_class_of' e = ⟨M.parallel_cl e, parallel_class_iff_is_parallel_cl.mpr ⟨e,e.2,rfl⟩⟩ :=
rfl 

lemma parallel_cl_eq_of_parallel (hef : M.parallel e f) :
   M.parallel_cl e = M.parallel_cl f :=
M.ps.cl_eq_cl_of_rel hef 

lemma parallel_of_parallel_cl_eq_left (he : M.is_nonloop e)
(hef : M.parallel_cl e = M.parallel_cl f) : 
  M.parallel e f :=
by rwa [parallel_cl, parallel_cl, M.ps.cl_eq_cl_iff (parallel_refl_of_nonloop he)] at hef

instance coe_parallel_class_to_set : has_coe (M.parallel_class) (set α) := 
  ⟨subtype.val⟩ 
instance parallel_class_fintype : fintype M.parallel_class := 
by {unfold parallel_class, apply_instance} 

lemma mem_parallel_class_of (he : M.is_nonloop e) :
  e ∈ (parallel_class_of e he : set α) :=
by {show e ∈ M.parallel_cl e, rwa [mem_parallel_cl, parallel_refl_iff_nonloop]} 

@[simp] lemma coe_parallel_class_of (he : M.is_nonloop e) :
  (parallel_class_of e he : set α) = M.parallel_cl e := 
rfl 

lemma parallel_of_mems_parallel_class 
(hP : M.is_parallel_class P) (he : e ∈ P) (hf : f ∈ P) : 
  M.parallel e f := 
M.ps.rel_of_mems_class hP he hf

lemma nonloop_of_mem_parallel_class 
(heP : e ∈ P) (h : M.is_parallel_class P) :
  M.is_nonloop e := 
parallel_refl_iff_nonloop.mp (M.ps.rel_self_of_mem_class h heP)

lemma parallel_class_eq_cl_mem (hP : M.is_parallel_class P) (he : e ∈ P) :
  P = M.parallel_cl e := 
M.ps.class_eq_cl_mem hP he 

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
  simp only [mem_diff, mem_set_of_eq, mem_cl_iff_r, rank_nonloop he, 
    union_singleton, ←nonloop_iff_not_mem_loops], 
  split, { rintros ⟨hx,he,hxe⟩, split; assumption,  }, 
  rintros ⟨hxe,hx⟩, exact ⟨hx,he,hxe⟩, 
end

lemma cl_eq_parallel_cl_union_loops (M : matroid α) (e : α) :
  M.cl {e} = M.parallel_cl e ∪ M.loops :=
begin
  rw [parallel_cl_eq_cl_minus_loops, diff_union_self, union_comm, ← subset_iff_union_eq_right], 
  apply loops_subset_cl, 
end

lemma rank_parallel_cl (he : M.is_nonloop e) : 
  M.r (M.parallel_cl e) = 1 := 
by rwa [parallel_cl_eq_cl_minus_loops, rank_eq_rank_diff_rank_zero _ M.rank_loops, 
        rank_cl, ←nonloop_iff_r]

lemma parallel_class_eq_cl_nonloop_diff_loops : 
  M.is_parallel_class P ↔ P.nonempty ∧ (∀ e ∈ P, P = M.cl {e} \ M.loops ) := 
begin
  rw [parallel_class_iff_is_parallel_cl], 
  simp_rw [←parallel_cl_eq_cl_minus_loops],  
  split, 
  { rintros ⟨a, ha, rfl⟩, 
    rw parallel_cl_nonempty_iff_nonloop, 
    refine ⟨ha, λ e he, parallel_cl_eq_of_parallel _⟩,
    symmetry, rwa mem_parallel_cl at he, }, 
  rintros ⟨⟨e,he⟩,h⟩, 
  obtain rfl := h e he,  
  rw [mem_parallel_cl, parallel_refl_iff_nonloop] at he, 
  exact ⟨e, he, rfl⟩, 
end

/-- the natural equivalence between points and parallel classes in a matroid -/
def parallel_class_point_equiv (M : matroid α) : 
  M.parallel_class ≃ M.point := 
{ to_fun := λ P, ⟨P.val ∪ M.loops, 
  let ⟨e,he,h⟩ := parallel_class_iff_is_parallel_cl.mp P.property in by 
  { simp_rw [h, point_iff_cl_nonloop, parallel_cl_eq_cl_minus_loops, diff_union_self, union_comm, 
    subset_iff_union_eq_left.mp (M.loops_subset_cl {e})],
    exact ⟨e,he,rfl⟩, }⟩, 
inv_fun := λ P, ⟨P.val \ M.loops, 
  let ⟨e,he,hP⟩ := point_iff_cl_nonloop.mp P.2 in by 
  { rw [hP, ← parallel_cl_eq_cl_minus_loops, parallel_class_iff_is_parallel_cl], 
    refine ⟨e, he, rfl⟩,}⟩,
left_inv := λ P, let ⟨e,he,h⟩ := parallel_class_iff_is_parallel_cl.mp P.2 in by 
  { simp_rw [h, union_diff_right, parallel_cl_eq_cl_minus_loops, diff_diff, union_self, 
    ← parallel_cl_eq_cl_minus_loops, ← h], simp, },
right_inv := λ P, let ⟨e,he,hP⟩ := point_iff_cl_nonloop.mp P.2 in by 
  { dsimp only, simp_rw [hP, diff_union_self, union_comm, 
    subset_iff_union_eq_left.mp (M.loops_subset_cl {e}), ←hP],simp, }}

@[simp] lemma parallel_class_point_equiv_apply (P : M.parallel_class) :
  M.parallel_class_point_equiv P 
= ⟨P.val ∪ M.loops, 
  let ⟨e,he,h⟩ := parallel_class_iff_is_parallel_cl.mp P.property in by 
  { simp_rw [h, point_iff_cl_nonloop, parallel_cl_eq_cl_minus_loops, diff_union_self, union_comm, 
    subset_iff_union_eq_left.mp (M.loops_subset_cl {e})],
    exact ⟨e,he,rfl⟩, }⟩ :=
rfl

@[simp] lemma parallel_class_point_equiv_apply_symm (P : M.point) :
  (M.parallel_class_point_equiv.symm P) 
= ⟨P.val \ M.loops, 
  let ⟨e,he,hP⟩ := point_iff_cl_nonloop.mp P.2 in by 
  { rw [hP, ← parallel_cl_eq_cl_minus_loops, parallel_class_iff_is_parallel_cl], 
    refine ⟨e, he, rfl⟩,}⟩ :=
rfl 

lemma parallel_class_nonempty (P : M.parallel_class) :
  set.nonempty (P : set α) := 
(parallel_class_eq_cl_nonloop_diff_loops.mp P.property).1

lemma nonloop_of_parallel_cl_is_parallel_class {P : M.parallel_class} 
(h : (P : set α) = (M.parallel_cl e)) : 
  M.is_nonloop e := 
begin
  by_contra hn, 
  rw parallel_cl_loop_empty (loop_iff_not_nonloop.mpr hn) at h, 
  exact nonempty.ne_empty (parallel_class_nonempty P) h, 
end

lemma parallel_class_eq_parallel_cl_of_mem {P : M.parallel_class} (he : e ∈ (P : set α)) :
  (P : set α) = M.parallel_cl e := 
begin
  obtain ⟨-, h'⟩ := parallel_class_eq_cl_nonloop_diff_loops.mp P.property, 
  simp_rw [←parallel_cl_eq_cl_minus_loops, subtype.val_eq_coe] at h', 
  rwa ←(h' e he), 
end 

lemma parallel_class_is_cl_diff_loops (P : M.parallel_class) : 
  ∃ e ∈ (P : set α), M.is_nonloop e ∧ (P : set α) = M.cl {e} \ M.loops :=
begin
  rcases parallel_class_eq_cl_nonloop_diff_loops.mp P.property with ⟨⟨e,he⟩,hP⟩, 
  exact ⟨e,he,nonloop_of_mem_parallel_class he P.property, hP e he⟩, 
end

lemma parallel_class_is_parallel_cl_nonloop (P : M.parallel_class) :
  ∃ e ∈ (P : set α), M.is_nonloop e ∧ (P : set α) = M.parallel_cl e :=
begin
  have := parallel_class_is_cl_diff_loops P, 
  simp_rw ←parallel_cl_eq_cl_minus_loops at this,
  assumption
end 

lemma parallel_class_is_parallel_cl (P : M.parallel_class) :
  ∃ e, (P : set α) = M.parallel_cl e :=
by {obtain ⟨e,he,he'⟩ := parallel_class_is_parallel_cl_nonloop P, use ⟨e,he'.2⟩,   }

lemma mem_parallel_class_iff_parallel_cl  {P : M.parallel_class} : 
  e ∈ (P : set α) ↔ (P : set α) = M.parallel_cl e :=
begin
  refine ⟨λ h, parallel_class_eq_parallel_cl_of_mem h, λ h, _⟩, 
  rw [h, parallel_cl, M.ps.mem_cl_iff],--, mem_set_of_eq], 
  exact parallel_refl_of_nonloop (nonloop_of_parallel_cl_is_parallel_class h),
end 

lemma rank_parallel_class (M : matroid α) (P : M.parallel_class ) : 
  M.r P = 1 := 
begin 
  obtain ⟨e,heP,he, hP⟩ := parallel_class_is_parallel_cl_nonloop P, 
  rw hP, 
  apply rank_parallel_cl he
end 

lemma parallel_class_eq_of_nonempty_inter {P₁ P₂ : M.parallel_class} 
(h : set.nonempty (P₁ ∩ P₂ : set α)) : 
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

lemma disj_of_distinct_parallel_classes {P₁ P₂ : M.parallel_class} (h : P₁ ≠ P₂) :
  disjoint (P₁ : set α) (P₂ : set α) := 
begin
  by_contra hn, rcases not_disjoint_iff.mp hn with ⟨e,⟨h₁,h₂⟩⟩, 
  exact h (parallel_class_eq_of_nonempty_inter ⟨e,mem_inter h₁ h₂⟩),
end

lemma parallel_class_eq_of_mem_both {P₁ P₂ : M.parallel_class} {x : α}
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
def union_parallel_classes (S : set M.parallel_class) : set α := 
  ⋃₀ (coe '' S)

lemma mem_union_parallel_classes {S : set M.parallel_class} : 
  e ∈ union_parallel_classes S ↔ ∃ (he : M.is_nonloop e), (parallel_class_of e he) ∈ S  := 
begin
  simp_rw [union_parallel_classes, mem_sUnion], split, 
  { rintros ⟨X, hX, heX⟩, 
    obtain ⟨⟨P,hP⟩,hP₁,rfl⟩ := (mem_image _ _ _).mp hX,
    obtain ⟨f, hf, rfl⟩ := rep_parallel_class hP, 
    use nonloop_of_mem_parallel_class heX hP, 
    convert hP₁ using 1, 
    rw [parallel_class_of, subtype.mk_eq_mk],
    apply parallel_cl_eq_of_parallel,  
    rwa [subtype.coe_mk, mem_parallel_cl] at heX},
  rintros ⟨he, heP⟩, 
  refine ⟨M.parallel_cl e, _,_⟩, 
  { simp only [mem_image], exact ⟨_, heP, rfl⟩}, 
  rwa [mem_parallel_cl, parallel_refl_iff_nonloop], 
end

lemma union_union_parallel_classes (S₁ S₂ : set M.parallel_class) : 
  union_parallel_classes (S₁ ∪ S₂) = union_parallel_classes S₁ ∪ union_parallel_classes S₂ :=
by simp_rw [union_parallel_classes, image_union, sUnion_union]


lemma inter_union_parallel_classes (S₁ S₂ : set M.parallel_class) : 
  union_parallel_classes (S₁ ∩ S₂) = union_parallel_classes S₁ ∩ union_parallel_classes S₂ :=
begin
  simp_rw [union_parallel_classes, ←image_inter (subtype.coe_injective)], 
  apply pairwise_disjoint_inter_sUnion (parallel_class_set_disjoint M); 
  apply image_subset_range, 
end

/-- the set of parallel classes containing an element of X-/
def parallel_cl_image_of (M : matroid α) (X : set α) :
  set (M.parallel_class) := 
{P | (X ∩ P).nonempty} 

lemma mem_parallel_cl_image_of_iff {P : M.parallel_class} : 
  P ∈ M.parallel_cl_image_of X ↔ (X ∩ P).nonempty := 
by simp [parallel_cl_image_of]


lemma rank_eq_rank_parallel_cl_image_of (M : matroid α) (X : set α) :
  M.r X = M.r (union_parallel_classes (M.parallel_cl_image_of X)) :=
begin
  refine rank_eq_rank_of_parallel_covered 
    (λ x hx hnl, ⟨x, _, parallel_refl_of_nonloop hnl⟩) (λ y hy hnl, _), 
  { simp_rw [mem_union_parallel_classes, mem_parallel_cl_image_of_iff], 
    exact ⟨hnl, ⟨x, mem_inter hx (by simpa [mem_parallel_cl] using parallel_refl_of_nonloop hnl)⟩⟩}, 
  simp_rw [mem_union_parallel_classes, mem_parallel_cl_image_of_iff] at hy, 
  obtain ⟨he', ⟨x, hx⟩⟩ := hy, 
  simp only [mem_inter_eq, coe_parallel_class_of, mem_parallel_cl] at hx, 
  exact ⟨x, hx.1, parallel_symm' hx.2⟩, 
end




--lemma intersecting_parallel_nl_classes_eq (S : set M.parallel_nl_class) : set α :=

/- property that a map sends parallel classes to representatives -/
def is_transversal (f : M.parallel_class → α) :=
  ∀ P, M.parallel_cl (f P) = (P : set α)

def transversal (M : matroid α) := 
  { f : M.parallel_class → α // is_transversal f}

instance coe_transversal  : has_coe_to_fun M.transversal := { F := _, coe := subtype.val }

lemma transversal_def (f : M.transversal) (P : M.parallel_class) : 
  M.parallel_cl (f P) = (P : set α) := 
(f.property P)

lemma transversal_def' (f : M.transversal) (hP : M.is_parallel_class P) :
  M.parallel_cl (f ⟨P,hP⟩) = P := 
f.property ⟨P,hP⟩ 

lemma nonloop_of_range_transversal (f : M.transversal) (P : M.parallel_class) : 
  M.is_nonloop (f P) := 
nonloop_of_parallel_cl_is_parallel_class (f.property P).symm

lemma exists_transversal (M : matroid α) : 
  ∃ (f : M.parallel_class → α), is_transversal f := 
⟨λ P, (classical.some (parallel_class_is_parallel_cl P)), 
 λ P, (classical.some_spec (parallel_class_is_parallel_cl P)).symm ⟩ 

def choose_transversal (M : matroid α) : M.transversal  :=
classical.indefinite_description _ (M.exists_transversal)

lemma transversal_subset_union (f : M.transversal) (S : set M.parallel_class) :
  f '' S ⊆ union_parallel_classes S :=
begin
  intros x hx, 
  obtain ⟨P, hP, rfl⟩ := (mem_image _ _ _).mp hx, 
  rw mem_union_parallel_classes, 
  refine ⟨nonloop_of_range_transversal f _,_⟩, 
  convert hP, 
  simp [parallel_class_of, transversal_def], 
end 


lemma eq_of_parallel_range_transversal {P Q : M.parallel_class} (f : M.transversal)
(h : M.parallel (f P) (f Q)) : 
  P = Q :=
begin
  cases P with P hP, cases Q with Q hQ, 
  rw [subtype.mk_eq_mk, ←transversal_def' f hP, ←transversal_def' f hQ],  
  have := parallel_symm' h, 
  ext, simp_rw mem_parallel_cl, 
  split; {intro h', transitivity, assumption, assumption,}, 
end

lemma transversal_inj (f : M.transversal) :
  function.injective f := 
begin
  intros P Q hPQ, 
  apply eq_of_parallel_range_transversal f, rw hPQ, 
  apply parallel_refl_of_nonloop (nonloop_of_range_transversal _ _),  
end


lemma size_image_transversal (f : M.transversal)
(S : set M.parallel_class) :
  size (f '' S) = size S := 
size_image_inj (transversal_inj f) S

lemma rank_img_transversal (f : M.transversal)
(S : set M.parallel_class) :
  M.r (union_parallel_classes S) = M.r (f '' S) :=
begin
  refine (rank_eq_rank_of_parallel_ext (transversal_subset_union f _) (λ y hy, _)).symm, 
  rcases y with ⟨y,hy'⟩, 
  rcases mem_union_parallel_classes.mp hy' with ⟨hy_nl,hP⟩, 
  set PY := parallel_class_of y hy_nl with hPY, 
  refine ⟨ ⟨f PY, _ ⟩, _⟩, apply mem_image_of_mem _ hP, 
  simp_rw [PY, subtype.coe_mk], 
  rwa [parallel_comm, ← mem_parallel_cl, transversal_def, coe_parallel_class_of, mem_parallel_cl,
  parallel_refl_iff_nonloop], 
end

end matroid 