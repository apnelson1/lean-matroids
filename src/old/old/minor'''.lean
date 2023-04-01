/-  An alternative take on the definition of a minor, where we take a quotient. Very much WIP. -/

import ftype.basic set_tactic.solver
import .rankfun .dual

--noncomputable theory
open_locale classical
noncomputable theory

open ftype

variables {U₀ U V W: ftype}--[nonempty U₀]

--def img (emb : U₀ ↪ U) :=
--  λ (X : set U₀), emb.to_fun '' X

/- given an injection emb, and a set equal to the range of emb, outputs an equivalence between the
domain and the subtype corresponding to the range.
def subtype_inv_inj (emb : U₀ ↪ U){E : set U} (hE : E = set.range emb) : E ≃ U₀ :=  
let h : Π (y : E), (∃ x : U₀, emb x = y) :=
  by {rintros ⟨y,hy⟩, rw [hE, set.mem_range] at hy, cases hy with x hx, from ⟨x, by simp [hx]⟩},
 desc : Π (y : E), {x : U₀ // emb x = y} :=  
  λ y, classical.indefinite_description _ (h y) in
{
  to_fun := λ y, (desc y).val,
  inv_fun := λ x, ⟨emb x, by {rw [hE, set.mem_range], from ⟨x, rfl⟩} ⟩,
  left_inv := by {intros y, simp_rw (desc y).property, simp},
  right_inv := λ x, by {cases emb with f h_inj, from h_inj (desc ⟨f x,_⟩).property},
}
-/

def subset_embed (X : set U) : X ↪ U :=
{ to_fun := λ x, x.val,
  inj' := λ x y hxy, subtype.ext hxy}

def subset_to_subtype {X Y : set U} (hXY : X ⊆ Y) : set Y :=
  λ y, y.val ∈ X

/-- (invisible) equivalence between the class of subsets of R and the class of
 sets in the ftype corresponding to R -/
def subset_equiv {R : set U} : {X : set U // X ⊆ R} ≃ set (⟨R⟩ : ftype) :=
{ to_fun := λ X, {y | y.val ∈ X.val},
  inv_fun := λ Y, ⟨coe '' Y,by {intros y hy, cases hy with x hx, rw ←hx.2, exact x.2,} ⟩,
  left_inv := begin
    intro X, ext x, simp only [set.mem_image, subtype.coe_mk],
    refine ⟨λ h, _, λ h, ⟨⟨x,_⟩,⟨_,_⟩⟩⟩,
    { rcases h with ⟨x',h₁,h₂⟩, rw ←h₂, convert h₁,},
    { cases X, tauto, },
    { tauto, },
    simp,
  end,
  right_inv := begin
    intro X, ext x, cases x with x xp,  simp only [set.mem_set_of_eq],
    refine ⟨λ h, _, λ h, _⟩,
    {unfold_projs at h, rcases h with ⟨a,h1,h2⟩, simp_rw ←h2, convert h1, simp},
    exact ⟨⟨x,xp⟩, ⟨h,by simp⟩⟩,  
  end, }




/-- bundled isomorphism between two matroids -/
structure isom (M : matroid U) (N : matroid V) :=
  (bij: U ≃ V)
  (rank_preserving : M.r =  N.r ∘ (set.image bij))

instance coe_iso_to_fun {M : matroid U} {N : matroid V} : has_coe_to_fun (isom M N) :=
{F := λ (i : isom M N), (U → V), coe := λ i, i.bij}

/-- inverse of a matroid isomorphism -/
def inv{M: matroid U} {N: matroid V} (iso : isom M N) : isom N M :=
{
  bij := iso.bij.symm,
  rank_preserving :=
  by {rw iso.rank_preserving, ext X, convert rfl, convert rfl, ext x, simp},
}

def compose {M : matroid U} {N : matroid V} {O : matroid W} (i₁ : isom M N) (i₂ : isom N O) : isom M O :=
{
  bij := equiv.trans i₁.bij i₂.bij,
  rank_preserving :=
  begin
    ext X, rw [i₁.rank_preserving, i₂.rank_preserving], 
    simp only [equiv.to_fun_as_coe, ftype.ftype_coe, function.comp_app, equiv.coe_trans],
    apply congr_arg, ext x,  simp,
  end
}

-- making a hash of this one!
@[simp] lemma compose_inv_on_set {M: matroid U} {N: matroid V} (iso : isom M N) (X : set U) :
  ((inv iso).bij '' (iso.bij '' X)) = X :=
begin
  --unfold equiv.img,
  convert rfl, ext,
  rw set.mem_image,
  refine ⟨λ h, ⟨iso.bij x,⟨_,_⟩⟩,λ h, _⟩,
    {simp only [equiv.to_fun_as_coe, equiv.apply_eq_iff_eq, set.mem_image, exists_eq_right], from h },
    {simp[inv]},
    {rcases h with ⟨y,h1,h2⟩, rw set.mem_image at h1, rcases h1 with ⟨x', ⟨hx'1, hx'2⟩⟩, rw [←h2,←hx'2] , convert hx'1, rw inv, simp,}
end



variable {M : matroid U}



/-- structure describing a matroid and an embedding of its elements into U -/
@[ext] structure emb_mat (U : ftype) :=
  {U₀ : ftype}
  (mat : matroid U₀)
  (emb : U₀ ↪ U)

namespace emb_mat

def groundset (N : emb_mat U) : set U :=
  set.range N.emb

def strongly_iso (N₁ N₂ : emb_mat U) : Prop :=
  (∃ (φ : isom (N₁.mat) (N₂.mat)), ∀ x, N₁.emb x = N₂.emb (φ x))

lemma strong_iso_equiv :
  equivalence (λ (N₁ N₂ : emb_mat U), strongly_iso N₁ N₂) :=
begin
  refine ⟨λ N, _, λ N₁ N₂ hab, _, λ N₁ N₂ N₃ hab hbc, _⟩,
    {refine ⟨⟨equiv.refl _,_⟩,λ X, _⟩,
      {ext X, simp,},
      {apply congr_arg, unfold_coes, simp} },
    {cases hab with φ, refine ⟨inv φ, λ X, _⟩, rw [hab_h ((inv φ) X), inv], unfold_coes, simp},
  cases hab with i₁ h₁, cases hbc with i₂ h₂,
  from ⟨compose i₁ i₂, λ X, by {unfold_coes at *, simp [h₁,h₂,congr_arg, compose]}⟩, 
end

lemma strong_iso_same_groundset (N N' : emb_mat U) :
  strongly_iso N N' → N.groundset = N'.groundset  :=
begin
  rintros ⟨h₁,h₂⟩, ext,
  simp only [groundset, set.mem_range],
  simp_rw h₂,
  refine ⟨λ h, _, λ h, _⟩,
    {cases h with y hy, from ⟨_, hy⟩},
  cases h with y hy, use h₁.bij.inv_fun y, unfold_coes, simp [hy],
end

--def pullback_r (N : emb_mat U) : set (N.ground) → ℤ :=
--  λ X, N.mat.r ((N.emb.subtype_inv_inj (rfl : N.ground = set.range N.emb))'' X)

/-- mapped rank function of N, but defined on all subsets of U (elements not in image are ignored)-/
def pullback_r (N : emb_mat U) : set U → ℤ :=
  λ X, N.mat.r ({x : N.U₀ | N.emb x ∈ X })

lemma pullback_r_eq (N : emb_mat U) (X : set N.U₀) :
  N.mat.r X = N.pullback_r (N.emb.to_fun '' X) :=
begin
  unfold pullback_r, congr', ext x,
  simp only [set.mem_image, function.embedding.to_fun_eq_coe, set.mem_set_of_eq],
  refine ⟨λ h, _, λ h, _⟩,
    {use x, simp, from h},
  cases h with x' hx',
  convert hx'.1,
  from (N.emb.inj' hx'.2).symm,
end
  --ite (X ⊆ N.ground) (some 0 : option ℤ) (none : option ℤ)
 
  --N.mat.r ((N.emb.subtype_inv_inj (rfl : N.ground = set.range N.emb))'' X)

lemma strong_iso_same_pullback_r (N N' : emb_mat U) :
  strongly_iso N N' → N.pullback_r = N'.pullback_r :=
begin
  rintros ⟨⟨φ,hφ₁⟩, hφ₂⟩, ext X,
  unfold pullback_r, rw hφ₁,
  dsimp, congr', ext x',
  simp only [set.mem_image, set.mem_set_of_eq],
  simp_rw hφ₂,
  refine ⟨λ h, _, λ h, ⟨φ.inv_fun x',⟨_,by simp⟩⟩⟩,
    {rcases h with ⟨x, ⟨hx₁,hx₂⟩⟩, rw ←hx₂, from hx₁,},
  rw ←hφ₂,
  convert h, 
  rw hφ₂,
  congr', unfold_coes, simp,
end

/-- if E is equal to the groundset of N, then there is a natural equivalence between E and U₀ -/
def groundset_equiv (N : emb_mat U){E : set U} (hE : N.groundset = E) :
  N.U₀ ≃ (⟨E⟩ : ftype) :=
  ((equiv.set.range N.emb N.emb.inj').trans (equiv.set.of_eq hE))

--def pullback_r' (N : emb_mat U){E : set U} (hE : N.ground = E) : set E → ℤ :=



instance strong_iso_setoid (U : ftype) : setoid (emb_mat U) := ⟨strongly_iso, strong_iso_equiv⟩

end emb_mat

/-- a matroid_in U is a matroid embedded into some set of ements of U, modulo the range of the embedding-/
def matroid_in (U : ftype) := quot (λ (N N' : emb_mat U), N.strongly_iso N')

namespace matroid_in

/-- the groundset of N, viewed as a (set U)-/
def groundset : matroid_in U → set U := quotient.lift 
  (λ (N : emb_mat U), N.groundset) emb_mat.strong_iso_same_groundset

/-- the groundset of N, viewed as an ftype -/
def ground (N : matroid_in U) : ftype := ⟨N.groundset⟩

/-- the rank function of N as a function on set U (elements outside the groundset of N
are ignored)-/
def r : matroid_in U → (set U → ℤ) := quotient.lift
  (λ (N : emb_mat U), N.pullback_r) emb_mat.strong_iso_same_pullback_r

/-- the rank function of N as a function on sets of the ground ftype of N-/
def r_ftype (N : matroid_in U) : (set N.ground → ℤ) :=
  λ X, N.r ((λ x : N.ground, x.val)'' X )

/-- an equivalence class representative for N -/
def rep_spec (N : matroid_in U) : {N₀ : emb_mat U // ⟦N₀⟧ = N} :=
  classical.indefinite_description _ (quot.exists_rep N)

/-- the ground set of a representative is the ground set of a matroid_in -/
lemma ground_rep {N : matroid_in U} {N₀ : emb_mat U} (h : ⟦N₀⟧ = N) :
   N₀.groundset = N.groundset  :=
by {dsimp only [quotient.mk] at h, rw ←h, refl}


lemma r_eq_r_inter_groundset (N : matroid_in U) (X : set U) :
  N.r X = N.r (X ∩ N.groundset) :=
begin
  unfold matroid_in.groundset r emb_mat.pullback_r emb_mat.groundset,
  rcases rep_spec N with ⟨N₀,h⟩,
  simp [←h],
end

section preimages

variables {N : matroid_in U} {N₀ : emb_mat U}

/-- given an equivalence class representative N₀, pulls a set X back to the
ftype on which N₀ is defined -/
def rep_preimage (hN : ⟦N₀⟧ = N) (X : set N.ground) :=
  N₀.groundset_equiv (ground_rep hN) ⁻¹' X

lemma rep_preimage_on_size (hN : ⟦N₀⟧ = N) (X : set N.ground) :
  size (rep_preimage hN X) = size X :=
by {apply size_preimage_equiv}

lemma rep_preimage_on_subset (hN : ⟦N₀⟧ = N){X Y : set N.ground} :
  X ⊆ Y → rep_preimage hN X ⊆ rep_preimage hN Y :=
λ h, set.preimage_mono h


lemma r_rep (hN : ⟦N₀⟧ = N) (X : set N.ground) :
  r_ftype N X = N₀.mat.r (rep_preimage hN X) :=
begin
  unfold r_ftype r,
  simp_rw ←hN,
  simp only [quotient.lift_mk],
  unfold emb_mat.pullback_r, apply congr_arg, ext x,
  rw [rep_preimage],
  simp only [set.mem_set_of_eq, emb_mat.groundset_equiv ], simp,
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨y,h,h'⟩, simp_rw ←h', convert h, simp,},
  use N₀.emb x,
  { unfold matroid_in.groundset, rw ←hN, simp only [quotient.lift_mk], unfold emb_mat.groundset, simp,},
  exact ⟨h, by simp⟩,
end

end preimages

def as_matroid (N : matroid_in U) : matroid N.ground :=
{
  r := N.r_ftype,
  R0 := λ X, let ⟨N₀,h⟩ := rep_spec N in by
  {rw r_rep h X, apply N₀.mat.R0, },
  R1 := λ X, let ⟨N₀,h⟩ := rep_spec N in by
  {rw [r_rep h X, ←rep_preimage_on_size h], apply N₀.mat.R1,},
  R2 := λ X Y hXY, let ⟨N₀,h⟩ := rep_spec N in by
  {repeat {rw r_rep h}, apply N₀.mat.R2, exact (rep_preimage_on_subset _ hXY),} ,
  R3 := λ X Y, let ⟨N₀,h⟩ := rep_spec N in by
  {repeat {rw r_rep h}, apply N₀.mat.R3,  }
}

lemma as_matroid_r_eq (N : matroid_in U) :
  ∀ X, N.r X = N.as_matroid.r (subset_equiv ⟨X ∩ N.groundset, by tidy⟩) :=
begin
  intro X,
  unfold matroid_in.as_matroid matroid_in.r_ftype subset_equiv,
  simp only [equiv.coe_fn_mk, subtype.coe_mk],
  rw r_eq_r_inter_groundset, congr',
  ext x, simp only [set.mem_image, set.mem_inter_eq,set.mem_set_of_eq,subtype.coe_mk],
  refine ⟨λ h, ⟨⟨x,h.2⟩,⟨⟨h.1,h.2⟩,by simp⟩⟩, λ h, _⟩,
  rcases h with ⟨x',⟨h,rfl⟩⟩,
  exact h,
end

/-- as_matroid is the canonical representative for a matroid_in -/
lemma as_matroid_is_rep (M : matroid_in U) :
  M = ⟦{mat := M.as_matroid, emb := function.embedding.subtype _ }⟧ :=
begin
  rcases M.rep_spec with ⟨M₀,h⟩, rw ←h, apply quotient.sound,
 
  simp only [has_equiv.equiv, setoid.r, emb_mat.strongly_iso, as_matroid, r_ftype],
  dsimp only [ftype.ftype_coe],
  refine ⟨⟨_,_⟩,λ x, _⟩,
  { refine emb_mat.groundset_equiv _ _, refl, },
  begin
    ext X, simp only [function.comp_app, r, emb_mat.pullback_r], unfold emb_mat.groundset_equiv, congr', ext x,
    simp only [set.mem_set_of_eq, set.image_congr, set.mem_image, exists_exists_and_eq_and, subtype.val_eq_coe],
    refine ⟨λ h, ⟨x,h, by simp⟩, λ h, _⟩,
    rcases h with ⟨a,ha,h⟩, simp at h,
    rw ←M₀.emb.inj' h, exact ha,
  end,
  refl,
end

/- lemma as_matroid_r_eq_subset (N : matroid_in U) :
  ∀ X : {X : set U // X ⊆ N.groundset}, N.r X.val = N.as_matroid.r (subset_equiv X) :=
begin
  intro X,
  convert as_matroid_r_eq N X.val,
 
end -/

--lemma iso_to (M₀ : emb_mat U) :

def as_matroid_in (M : matroid U) : matroid_in U :=
  ⟦{U₀ := U, emb := function.embedding.refl U, mat := M}⟧




instance coe_to_matroid_in : has_coe (matroid U) (matroid_in U) := ⟨λ M, as_matroid_in M⟩

def embed (M : matroid_in U) : M.ground ↪ U := subset_embed M.groundset

def subset_embed {M : matroid_in U} {R : set U} (hR : R ⊆ M.groundset) : R ↪ M.ground :=
{to_fun  := λ x, ⟨x.val, by {cases x, tauto}⟩,
 inj'    := λ x y hxy, by {simp only [subtype.mk_eq_mk] at hxy, exact subtype.eq hxy, } }

def nested_embed (M' M : matroid_in U) (hMM' : M'.groundset ⊆ M.groundset) : M'.ground ↪ M'.ground :=
{to_fun  := λ x, ⟨x.val, by simp⟩,
 inj'    := λ x y hxy, by {convert hxy; simp,} }

--set_option pp.proofs true

def matroid_in_ext (M M' : matroid_in U) :
  M.groundset = M'.groundset → M.r = M'.r → M = M' :=
begin
  intros h h',
  rw [as_matroid_is_rep M, as_matroid_is_rep M', quotient.sound], 
  refine ⟨⟨_,_⟩,λ x, _⟩,
  {exact {to_fun := λ x, ⟨x.val, by {rw ←h, exact x.property,}⟩ ,
          inv_fun := λ x, ⟨x.val, by {rw h, exact x.property,}⟩,
          left_inv := λ x, by {dsimp only, simp,},
          right_inv := λ x, by {dsimp only, simp,}}, },
  begin
    simp_rw h',
    simp only [as_matroid, r_ftype], --simp_rw h',
    ext X, simp only [set.image_congr, function.comp_app, subtype.val_eq_coe], rw h',
    apply congr_arg, ext x, dsimp only [ftype.ftype_coe],
    simp only [set.image_congr, set.mem_image, exists_exists_and_eq_and, subtype.val_eq_coe],
    refine ⟨λ hx,_, λ hx, _⟩,
    { rcases hx with ⟨y,h₁,rfl⟩, exact ⟨y,h₁, by simp⟩,  },
    rcases hx with ⟨⟨y, hy⟩, hy', rfl⟩, refine ⟨⟨y,hy⟩,⟨hy',_⟩⟩, simp,
  end,
  refl,
end



def from_matroid_on_subtype {E : set U} (M : matroid ⟨E⟩) :  matroid_in U :=
⟦{mat := M, emb := function.embedding.subtype _}⟧

lemma groundset_correct {E : set U} (M : matroid ⟨E⟩) :
  (from_matroid_on_subtype M).groundset = E :=
by {unfold from_matroid_on_subtype groundset emb_mat.groundset, simp}

lemma rank_correct {E : set U} (M : matroid ⟨E⟩) (X : set U) :
  (from_matroid_on_subtype M).r X = M.r ((λ x, x.val) '' X) ∩ {e}   :=
by {unfold from_matroid_on_subtype groundset emb_mat.groundset, simp}



end matroid_in

section minor

/-- minor relation between two matroid_in U-/
def is_minor (N M : matroid_in U) : Prop :=
  (N.groundset ⊆ M.groundset) ∧
  ∃ C ⊆ M.groundset \ N.groundset, (∀ X ⊆ N.groundset, N.r X = M.r (X ∪ C) - M.r C) 

/-- minor relation between a matroid_in U and a matroid U -/
def is_minor_of (N : matroid_in U) (M : matroid U) :=
  is_minor N M

/-- N is isomorphic to a minor of M -/
def is_emb_minor (N : matroid U₀) (M : matroid U) :=
  ∃ emb : U₀ ↪ U, is_minor_of ⟦(⟨N,emb⟩:emb_mat U)⟧ M 

lemma minor_trans: transitive (λ (M₁ M₂ : matroid_in U), is_minor M₁ M₂) :=
begin
  rintros M₁ M₂ M₃ ⟨h1,⟨C₁,hC₁,h1'⟩⟩ ⟨h2,⟨C₂,hC₂,h2'⟩⟩,
  refine ⟨subset.trans h1 h2,⟨C₁ ∪ C₂,⟨_,λ X hX, _⟩⟩⟩,
  ----
  { convert set.union_subset_union hC₁ hC₂, ext,
    simp only [ftype.diff_eq, set.mem_inter_eq, set.mem_union_eq, set.mem_compl_eq],
    tauto, },
  -- set_solver should work for the goal above, but it is glacial
  have hC₁M₂: C₁ ⊆ M₂.groundset := by
  { intros x hx, simp only [ftype.diff_eq, set.subset_inter_iff] at hC₁, tauto,},
  rw [h1' X hX, h2' (X ∪ C₁) _, h2' C₁ hC₁M₂, ←union_assoc],  ring,
  exact union_of_subsets (subset.trans hX h1) hC₁M₂,
end

 def contract_to_matroid (M : matroid_in U) (C : set U) : matroid ⟨(M.groundset \ C : set U)⟩ :=
let mtype : ftype := ⟨(M.groundset \ C : set U)⟩,
φ : mtype → U := λ x, x.val  in 
{ r := λ X, M.r (φ '' X ∪ C) - M.r C,
  R0 :=
  begin
    intro X, dsimp only,
    repeat {rw matroid_in.as_matroid_r_eq},
    simp only [sub_nonneg],
    apply M.as_matroid.R2,
    unfold subset_equiv,
    simp, tauto,
  end,
  R1 :=
  begin
    sorry,
  end,
  R2 := sorry,
  R3 := sorry }

def contract_to_matroid_in (M : matroid_in U) (C : set U) : matroid_in U :=
  matroid_in_from_matroid_on_subtype (contract_to_matroid M C)

def delete_to_matroid (M: matroid_in U) (D : set U) : matroid ⟨(M.groundset \ D : set U)⟩  :=
let mtype : ftype := ⟨(M.groundset \ D : set U)⟩,
φ : mtype → U := λ x, x.val  in 
{ r := λ X, M.r (φ '' X),
  R0 := sorry,
  R1 :=
  begin
    sorry,
  end,
  R2 := sorry,
  R3 := sorry }

def delete_to_matroid_in (M : matroid_in U) (D : set U) : matroid_in U :=
  matroid_in_from_matroid_on_subtype (delete_to_matroid M D)

lemma foo (M : matroid_in U){C D : set U} (hi : C ∩ D = ∅) (hu : C ∪ D ⊆ M.groundset) :
  delete_to_matroid_in (contract_to_matroid_in M C) D =  contract_to_matroid_in (delete_to_matroid_in M D) C :=
begin
  apply matroid_in.matroid_in_ext,
  unfold delete_to_matroid_in contract_to_matroid_in, repeat {rw groundset_correct}, set_solver, 
  --simp, sorry,
end




/-- returns the contraction of C in M as a minor on a subtype-/
def contract_to_emb (M : matroid_in U) (C : set M.ground) : emb_mat U :=
{
  U₀ := ⟨(Cᶜ : set M.ground)⟩,
  mat := sorry,
  emb := (function.embedding.subtype (λ x, x ∈ Cᶜ)).trans M.embed, 
}

end minor

/- the rank function given by N when applied to a subset of the embedded ground set of N.  -/


--def is_minor (N : emb_mat U) (M : matroid U) :=
  --∃ C, C ∩ N.ground = ∅ ∧ ∀ X : set U₀, N.mat.r


--def is_minor {U : ftype} (N : emb_mat U) (M : matroid U) :=
--  ∃ C : set U, C ∩ N.ground = ∅ ∧ ∀

/-structure emb_minor' (M : matroid U) :=
  {U₀ : ftype}
  (mat : matroid U₀)
  (emb : U₀ ↪ U)
  (C : set U)
  (C_disj : C ∩ set.range emb = ∅)
  (minor_rank : mat.r = λ X, M.r (emb '' X ∪ C) - M.r C)-/


/-

/- the ground set of an emb_minor, expressed as a set of elements of M -/
def ground (N : emb_minor M) : set U := set.range N.emb

--def C (N : emb_minor M) : set U := classical.some N.minor_rank

def D (N : emb_minor M) : set U := (N.ground ∪ N.C)ᶜ

lemma def_ground (N : emb_minor M) : N.ground = set.range N.emb  := rfl

lemma C_ground_inter_empty (N : emb_minor M) :
  N.C ∩ N.ground = ∅ :=
by {rw ground, from N.C_disj,}

lemma D_ground_inter_empty (N : emb_minor M) :
  N.D ∩ N.ground = ∅ :=
by {rw [D], have := C_ground_inter_empty N, set_solver,}

lemma C_D_inter_empty (N : emb_minor M) :
  N.C ∩ N.D = ∅ :=
by {rw D, have := C_ground_inter_empty N, set_solver,}

lemma C_union_D_eq_ground_compl (N : emb_minor M) :
  (N.C ∪ N.D) = N.groundᶜ :=
by {rw [D], have := N.C_ground_inter_empty, set_solver,}

lemma emb_minor_r (N : emb_minor M) (X : set N.U₀) :
  N.mat.r X = M.r (N.emb '' X ∪ N.C) - M.r N.C :=
by rw N.minor_rank

/- the rank function given by N when applied to a subset of the embedded ground set of N.  -/
def pullback_r (N : emb_minor M) : set (N.ground) → ℤ :=
  λ X, N.mat.r ((N.emb.subtype_inv_inj (rfl : N.ground = set.range N.emb))'' X)

/- two embedded minors of M are strongly isomorphic if the associated matroids are related
by an isomorphism that commutes with the respective embeddings into M. -/
def strongly_iso (N₁ N₂ : emb_minor M) : Prop :=
  (∃ (φ : isom (N₁.mat) (N₂.mat)), ∀ x, N₁.emb x = N₂.emb (φ x))

/- existence of a strong isomorphism is an equivalence relation on embedded minors of M.
    Equivalence classes of this relation correspond to actual 'labelled' minors of M    -/
lemma strong_iso_equiv :
  equivalence (λ (N₁ N₂ : emb_minor M), strongly_iso N₁ N₂) :=
begin
  refine ⟨λ N, _, λ N₁ N₂ hab, _, λ N₁ N₂ N₃ hab hbc, _⟩,
    {refine ⟨⟨equiv.refl _,_⟩,λ X, _⟩,
      {simp [equiv.img], },
      {apply congr_arg, unfold_coes, simp} },
    {cases hab with φ, refine ⟨inv φ, λ X, _⟩, rw [hab_h ((inv φ) X), inv], unfold_coes, simp},
  cases hab with i₁ h₁, cases hbc with i₂ h₂,
  from ⟨compose i₁ i₂, λ X, by {unfold_coes at *, simp [h₁,h₂,congr_arg, compose]}⟩, 
end

/- the ground set is an invariant of equivalence classes under strong isomorphism -/
lemma strong_iso_same_groundset (N N' : emb_minor M) :
  strongly_iso N N' → N.ground = N'.ground  :=
begin
  rintros ⟨h₁,h₂⟩, ext,
  simp only [ground, set.mem_range],
  simp_rw h₂,
  refine ⟨λ h, _, λ h, _⟩,
    {cases h with y hy, from ⟨_, hy⟩},
  cases h with y hy, use h₁.bij.inv_fun y, unfold_coes, simp [hy],
end


instance strong_iso_setoid : setoid (emb_minor M) := ⟨strongly_iso, strong_iso_equiv⟩


end emb_minor


--variables {M : matroid U} [setoid (emb_minor_of M)]
def minor (M : matroid U) := quot (λ (N N' : emb_minor M), N.strongly_iso N')

namespace minor

def emb_to_minor (M : matroid U) := @quotient.mk (emb_minor M) _

/- returns the ground set of a minor of M (as a subset of the ftype for M) -/
def ground {M : matroid U} : minor M → set U := quotient.lift 
  (λ (N : emb_minor M), N.ground )
  (λ N N' hNN', emb_minor.strong_iso_same_groundset N N' hNN' )

end minor

-/
