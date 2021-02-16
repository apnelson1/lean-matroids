import prelim.collections prelim.size prelim.induction prelim.minmax
import .rankfun
import tactic data.setoid.partition

noncomputable theory 
open_locale classical 

open set 
namespace matroid 

variables {U : Type}[fintype U]


/-- is a rank-zero element -/
def is_loop (M : matroid U) : U → Prop := 
  λ e, M.r {e} = 0 

/-- is a rank-one element -/
def is_nonloop (M : matroid U) : U → Prop := 
  λ e, M.r {e} = 1 

/-- is a loop of the dual -/
def is_coloop (M : matroid U) : U → Prop := 
  is_loop (dual M) 

/-- is not a coloop of the dual -/
def is_noncoloop (M : matroid U) : U → Prop := 
  is_coloop (dual M)

lemma nonloop_iff_r {M : matroid U}{e : U}:
  M.is_nonloop e ↔ M.r {e} = 1 := 
iff.rfl 

lemma nonloop_iff_indep {M : matroid U}{e : U}:
  M.is_nonloop e ↔ M.is_indep {e} := 
by rw [is_nonloop, indep_iff_r, size_singleton] 

lemma rank_nonloop {M : matroid U}{e : U}:
  M.is_nonloop e → M.r {(e : U)} = 1 :=
by {unfold is_nonloop, from λ h, h}

lemma rank_loop {M : matroid U}{e : U}:
  M.is_loop e → M.r {e} = 0 :=
by {unfold is_loop, from λ h, h}

lemma loop_iff_elem_loops {M : matroid U} {e : U} : 
  M.is_loop e ↔ e ∈ M.loops := 
by {simp_rw [is_loop, ←singleton_subset_iff], from rank_zero_iff_subset_loops}  

lemma nonloop_iff_not_elem_loops {M : matroid U}{e : U}: 
  M.is_nonloop e ↔ e ∉ M.loops := 
begin
  simp_rw [is_nonloop, ←singleton_subset_iff, ←rank_zero_iff_subset_loops], 
  refine ⟨λ h h', by linarith, λ h, _⟩, 
  linarith [rank_single_ub M e, rank_gt_zero_of_ne h], 
end

lemma nonloop_iff_not_loop {M : matroid U} (e : U) : 
  M.is_nonloop e ↔ ¬ M.is_loop e := 
begin 
  unfold is_loop is_nonloop, refine ⟨λ h, _ ,λ h, _⟩,rw h ,
  simp only [not_false_iff, one_ne_zero], 
  have := M.rank_le_size {e}, rw size_singleton at this,       
  linarith [(ne.le_iff_lt (ne.symm h)).mp (M.rank_nonneg {e})],  
end

lemma coloop_iff_r {M : matroid U} (e : U) :
  M.is_coloop e ↔ M.r {e}ᶜ = M.r univ - 1 := 
begin
  unfold is_coloop is_loop, rw [dual_r,size_singleton],
  exact ⟨λh, by linarith,λ h, by linarith⟩,   
end

lemma coloop_iff_r_less {M : matroid U} (e : U) :
  M.is_coloop e ↔ M.r {e}ᶜ < M.r univ := 
begin
  unfold is_coloop is_loop, rw [dual_r,size_singleton],
  refine ⟨λh,by linarith,λ h,_⟩, 
  have := rank_diff_le_size_diff M (subset_univ {e}ᶜ), 
  rw [←size_compl, size_singleton] at this, 
  linarith [int.le_sub_one_iff.mpr h],
end

/-- nonloop as subtype -/
def nonloop (M : matroid U) : Type := { e : U // is_nonloop M e}

instance coe_nonloop {M : matroid U} : has_coe (nonloop M) (U) := ⟨λ e, e.val⟩  
--def noncoloop (M : matroid U) : Type := { e : U // is_nonloop (dual M) e}

lemma eq_nonloop_coe {M : matroid U}{e : U}(h : M.is_nonloop e): 
  e = coe (⟨e, h⟩ : M.nonloop) := 
rfl 

lemma rank_coe_nonloop {M : matroid U}(e : nonloop M) : 
  M.r {(e : U)} = 1 := 
rank_nonloop (e.2)

lemma coe_nonloop_indep {M : matroid U}(e : nonloop M) :
  M.is_indep {(e : U)} := 
by {rw [indep_iff_r], simp only [size_singleton, coe_coe], apply rank_coe_nonloop e,}

lemma rank_two_nonloops_lb {M : matroid U} (e f : nonloop M) :
  1 ≤ M.r ({e,f}) := 
begin
  rw ←union_singletons_eq_pair, 
  linarith [rank_coe_nonloop e, M.rank_mono_union_left {e} {f}],
end 

lemma rank_two_nonloops_ub {M : matroid U} (e f : nonloop M) : 
  M.r ({e,f}) ≤ 2 := 
begin
  rw ←union_singletons_eq_pair, 
  linarith [rank_coe_nonloop e, rank_coe_nonloop f, 
    M.rank_nonneg ({e} ∩ {f}), M.rank_submod {e} {f}], 
end 

section parallel 

/-- two nonloops have rank-one union -/
def parallel (M : matroid U) (e f : nonloop M) : Prop := 
  M.r ({e,f}) = 1 

/-- relation of being both nonloops and having a rank-one union. Equivalence classes 
include all singleton loops -/
def parallel' (M : matroid U)(e f : U): Prop := 
  M.is_nonloop e ∧ M.is_nonloop f ∧ M.r {e,f} = 1 

lemma parallel_of_parallel' {M : matroid U}{e f : U}(h : M.parallel' e f ):
  ∃ (he : M.is_nonloop e)(hf : M.is_nonloop f), M.parallel ⟨e,he⟩ ⟨f,hf⟩ :=
⟨h.1,h.2.1,h.2.2⟩

lemma parallel'_of_parallel {M : matroid U}{e f : M.nonloop}(h : M.parallel e f): 
  M.parallel' e.1 f.1 :=
⟨e.2,f.2,h⟩

lemma parallel'_iff_parallel {M : matroid U}{e f : U}:
  M.parallel' e f ↔ ∃ (he : M.is_nonloop e)(hf : M.is_nonloop f), M.parallel ⟨e,he⟩ ⟨f,hf⟩:= 
by tidy


--example (e f : U): ({e,f} : set U) = ({f,e} : set U) := pair_comm e f
--example (e : U): ({e,e} : set U) = {e} := by {exact pair_eq_singleton e,}

/-- parallel in dual -/
def series (M : matroid U) (e f : nonloop (dual M)): Prop := 
  (dual M).parallel e f 

lemma parallel_refl (M : matroid U): 
  reflexive M.parallel:= 
λ e, by {unfold parallel, rw pair_eq_singleton, exact e.property}

lemma parallel_symm (M : matroid U) : 
  symmetric M.parallel:= 
λ x y, by {simp_rw [parallel, pair_comm], tauto,}

lemma parallel_iff_dep {M: matroid U}{e f : nonloop M} : 
  M.parallel e f ↔ (e = f ∨ M.is_dep {e,f}) :=
begin
  unfold parallel, rw dep_iff_r,  refine ⟨λ h, ((or_iff_not_imp_left.mpr (λ hne, _))), λ h, _ ⟩,
  have := size_union_distinct_singles (λ h', hne (subtype.ext h')) , 
  rw h, unfold_coes at *, linarith,  
  cases h, rw [h, pair_eq_singleton], exact f.property, 
  have := rank_two_nonloops_lb e f, 
  have := size_union_singles_ub e.1 f.1,
  unfold_coes at *, rw ←int.le_sub_one_iff at h, linarith, 
end

lemma parallel_iff_cct {M: matroid U}{e f : nonloop M} : 
  M.parallel e f ↔ (e = f ∨ M.is_circuit {e,f}) :=
begin
  refine ⟨λ h, _, λ h, (parallel_iff_dep.mpr (or.imp_right _ h : (e = f) ∨ is_dep M ({e,f})))⟩, 
  replace h := parallel_iff_dep.mp h, cases h, exact or.inl h, apply or_iff_not_imp_left.mpr, intro h', 
  refine ⟨h,λ Y hY, _⟩, rcases ssubset_pair hY, 
  rw h_1, exact empty_indep M,  unfold_coes at h_1,  cases h_1; 
  {rw h_1, apply coe_nonloop_indep,},
  apply circuit_dep, 
end

lemma parallel_trans (M : matroid U) :
  transitive M.parallel :=
begin
  intros e f g hef hfg, unfold parallel at *, 
  have := M.rank_submod ({e,f}) ({f,g}), rw [hef, hfg] at this, 
  have h1 : 1 ≤ M.r (({e,f}) ∩ ({f,g})),  
  {rw ←rank_coe_nonloop f, refine M.rank_mono (subset_inter _ _ ); simp, },
  have h2 := M.rank_mono (_ : ({e,g} : set U)  ⊆ {e,f} ∪ {f,g}), swap, 
  {intro x, simp, tauto,  }, 
  linarith [(rank_two_nonloops_lb e g)],  
end

lemma parallel_is_equivalence (M : matroid U) : 
  equivalence M.parallel := 
  ⟨M.parallel_refl, M.parallel_symm, M.parallel_trans⟩

lemma series_is_equivalence (M : matroid U): 
  equivalence M.series :=
parallel_is_equivalence M.dual 


--reserve infixl ` ∼ `:75
--infix ` ∼ ` := @parallel _ _ _ 



instance parallel_setoid {M : matroid U} : setoid M.nonloop := ⟨M.parallel, M.parallel_is_equivalence⟩ 


/- a parallel class of M, implemented as an element of a quotient -/
def parallel_class (M: matroid U) : Type := @quotient M.nonloop (@matroid.parallel_setoid _ _ M) 

/- a parallel class of M, viewed as a set U -/
def as_set {M : matroid U}(C : M.parallel_class) : set U := 
  λ a, (∃ (h : M.is_nonloop a), ⟦(⟨a,h⟩ : M.nonloop)⟧ = C)


instance coe_parallel_class_to_set {M : matroid U}: has_coe (M.parallel_class) (set U) := ⟨@as_set _ _ M⟩ 

instance coe_parallel_quot_to_set {M : matroid U}: 
  has_coe (@quotient M.nonloop (@matroid.parallel_setoid _ _ M)) (set U) := ⟨@as_set _ _ M⟩ 

def as_set_mem_iff {M : matroid U}{a b : M.nonloop}: 
  b.val ∈ (⟦a⟧ : set U) ↔ a ≈ b := 
by {unfold_coes, simp only [as_set, quotient.eq, subtype.val_eq_coe], tidy}

def as_set_mem_iff' {M : matroid U}{a : M.nonloop}{b : U}: 
  b ∈ (⟦a⟧ : set U) ↔ ∃ (h : M.is_nonloop b), a ≈ ⟨b,h⟩ := 
by {unfold_coes, simp only [as_set, quotient.eq, subtype.val_eq_coe], tidy}
  
lemma as_set_inj {M : matroid U} {P P' : M.parallel_class} (h : (P : set U) = (P' : set U)):
  P = P' := 
begin 
  rw ext_iff at h, 
  rcases quotient.exists_rep P with ⟨⟨a,ha⟩,rfl⟩,
  rcases (h a).mp ⟨ha,rfl⟩ with ⟨h',h''⟩, 
  rw ←h'', 
end

lemma parallel'_iff {M : matroid U}{e f : U}: 
  M.parallel' e f ↔ ∃ (P : M.parallel_class), e ∈ (P : set U) ∧ f ∈ (P : set U) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨he,hf, hef⟩ := h, 
    use ⟦⟨e,he⟩⟧, 
    rw [as_set_mem_iff', as_set_mem_iff'],  
    refine ⟨⟨he, quotient.eq.mp rfl⟩, ⟨hf,hef⟩⟩},
  rcases h with ⟨P,he,hf⟩, 
  rcases P.exists_rep with ⟨a,rfl⟩, 
  rw as_set_mem_iff' at *, 
  rcases he with ⟨he, hae⟩, rcases hf with ⟨hf, haf⟩, 
  exact ⟨he,hf,setoid.trans (setoid.symm hae) haf,⟩, 
end 

def parallel_class_of {M : matroid U}{e : U}(he : M.is_nonloop e) : set U := 
  ⟦@id M.nonloop ⟨e,he⟩⟧


/-
lemma parallel_iff_exists_parallel_class {M : matroid U}{e f : M.nonloop}: 
  M.parallel e f ↔ ∃ P : M.parallel_class, e ∈ P ∧ f ∈ (P : set U) :=
begin
  
  
end -/

/-

def parallel_classes_set (M : matroid U):= 
  M.parallel_setoid.classes 

lemma parallel_iff_setoid_rel {M : matroid U}{e f : M.nonloop} : 
  M.parallel e f ↔ ∃ X : M.parallel_classes_set, e ∈ X.val ∧ f ∈ X.val := 
begin
  rw [←parallel_setoid_rel, setoid.rel_iff_exists_classes], 
  refine ⟨λ h, _, λ h, _⟩, 
  rcases h with ⟨Y,hY,he,hf⟩, exact ⟨⟨Y,hY⟩,he,hf⟩, 
  rcases h with ⟨⟨Y,hY⟩,he,hf⟩, exact ⟨Y,hY,he,hf⟩, 
end

def is_parallel_class (M : matroid U)(X : set U) :=
  ∃ S : M.parallel_classes_set, X = coe '' S.val 

lemma exists_unique_parallel_class {M : matroid U}(e : M.nonloop): 
  ∃! S : M.parallel_classes_set, e ∈ S.val := 
begin
  rw parallel_classes_set, 
  rcases @setoid.classes_eqv_classes _ M.parallel_setoid e with ⟨T,⟨⟨hT,⟨he,-⟩⟩,h⟩⟩, 
  refine ⟨⟨T,hT⟩,⟨he,_⟩⟩,  
  simp_rw [exists_unique_iff_exists] at h, 
  rintros ⟨T',hT'⟩ heT', 
  specialize h T' ⟨hT',heT'⟩, 
  rwa [subtype.mk_eq_mk], 
end

lemma nonloop_of_mem_parallel_class {M : matroid U}{X : set U}(hX: M.is_parallel_class X)(e : X): 
  M.is_nonloop e :=
begin
  rw [is_parallel_class, parallel_classes_set] at hX, rcases hX with ⟨⟨S,hS⟩,rfl⟩,
  rcases e with ⟨e,he⟩, 
  rcases (mem_image _ _ _).mp he with ⟨w,⟨hw, rfl⟩⟩,
  exact w.property, 
end

lemma parallel_of_mems_parallel_class {M : matroid U}{X : set U}(hX: M.is_parallel_class X)(e f : X): 
  ∃ (he : M.is_nonloop e)(hf : M.is_nonloop f), M.parallel ⟨e,he⟩ ⟨f,hf⟩ :=
begin
  rw [is_parallel_class, parallel_classes_set] at hX, 
  refine ⟨nonloop_of_mem_parallel_class hX e, nonloop_of_mem_parallel_class hX f, _⟩, 
  rw parallel_iff_setoid_rel, 
  rcases hX with ⟨⟨S,hS⟩,rfl⟩, use ⟨S,hS⟩, tidy, 
end

lemma parallel_class_iff {M : matroid U}{X : set U}:
  M.is_parallel_class X 
  ↔ (∀ e : X, M.is_nonloop e) ∧ ∀ (e f : M.nonloop), M.parallel e f → (e.val ∈ X ↔ f.val ∈ X) :=
begin
  
  refine ⟨λ h, ⟨λ e, nonloop_of_mem_parallel_class h _, λ e f hef, _⟩, λ h, _⟩, 
  rcases parallel_iff_setoid_rel.mp hef with ⟨Y,hY⟩, 
  
end  

def parallel_class (M : matroid U) : Type := {X : set U // M.is_parallel_class X}

lemma point_iff_parallel_class_and_loops {M : matroid U} {P: set U} : 
  is_point M P ↔ ∃ X, is_parallel_class M X ∧ P = X ∪ M.loops:=
begin
     
end

-/

end parallel 

section simple 

def is_loopless (M : matroid U) := 
  ∀ X, size X ≤ 1 → M.is_indep X 

def is_simple (M : matroid U) :=
  ∀ X, size X ≤ 2 → M.is_indep X 

lemma loopless_iff_all_nonloops {M : matroid U} :
  M.is_loopless ↔ ∀ e, M.is_nonloop e :=
begin
  simp_rw [nonloop_iff_r, is_loopless, size_le_one_iff_empty_or_singleton, indep_iff_r],
  refine ⟨λ h, λ e, _, λ h, λ X hX, _⟩, 
  { rw ←size_singleton e, apply h, right, exact ⟨e,rfl⟩},
  rcases hX with (rfl | ⟨e,rfl⟩), simp, 
  rw [size_singleton, h e], 
end 

lemma simple_iff_no_loops_or_parallel_pairs {M : matroid U}:
  M.is_simple ↔ (∀ e, M.is_nonloop e) ∧ ∀ (e f : nonloop M), M.parallel e f → e = f :=
begin
  refine ⟨λ h, ⟨λ e, _, λ e f hef, _⟩,  λ h, λ X hX, _⟩, 
  
  { rw nonloop_iff_indep, apply h, rw size_singleton, norm_num}, 
  { rw [parallel] at hef, 
    suffices : (e : U) = (f : U), cases e, cases f, simpa, 
    by_contra hn,
    have := h {coe e, coe f} (by rw size_union_distinct_singles hn),  
    rw [indep_iff_r, hef, size_union_distinct_singles hn] at this, 
    norm_num at this, },
  
  rcases int.nonneg_le_two_iff (size_nonneg X) hX with (h0 | h1 | h2), 
  { rw size_zero_iff_empty at h0, rw h0, apply M.I1, },
  { rcases size_one_iff_eq_singleton.mp h1 with ⟨e,rfl⟩, rw ←nonloop_iff_indep, apply h.1, },
  rcases size_eq_two_iff_pair.mp h2 with ⟨e,f,hef,rfl⟩,
  rw [eq_nonloop_coe (h.1 e), eq_nonloop_coe (h.1 f)], 
  
  rw [indep_iff_not_dep], by_contra hn, push_neg at hn, 
  have h' := h.2 ⟨e, h.1 e⟩ ⟨f, h.1 f⟩, rw parallel_iff_dep at h',
  specialize h' (or.intro_right _ hn), rw [subtype.mk_eq_mk] at h',   
  exact hef h', 
end
end simple 
end matroid 

