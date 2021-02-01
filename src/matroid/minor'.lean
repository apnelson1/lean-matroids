import ftype.basic ftype.embed set_tactic.solver
import .rankfun .dual 

--noncomputable theory
open_locale classical
noncomputable theory 

open ftype 


variables {U₀ U V W: ftype}--[nonempty U₀]


--def embed := U ↪ V 



namespace function.embedding

def img (emb : U₀ ↪ U):=
  λ (X : set U₀), emb.to_fun '' X 

/-- given an injection emb, and a set equal to the range of emb, outputs an equivalence between the 
domain and the subtype corresponding to the range. -/ 
def subtype_inv_inj (emb : U₀ ↪ U){E : set U}(hE : E = set.range emb) : E ≃ U₀ :=   
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

end function.embedding 


namespace equiv 

def img (bij : U ≃ V) :=
  λ (X : set U), bij.to_fun '' X 

def inv_img (bij : U ≃ V) :=
  λ (X : set V), bij.to_fun ⁻¹' X

end equiv 

/-- bundled isomorphism between two matroids-/
structure isom (M : matroid U)(N : matroid V) := 
  (bij: U ≃ V)
  (rank_preserving : M.r =  N.r ∘ bij.img)

instance coe_iso_to_fun {M : matroid U}{N : matroid V}: has_coe_to_fun (isom M N) := 
{F := λ (i : isom M N), (U → V), coe := λ i, i.bij}

/-- inverse of a matroid isomorphism-/
def inv{M: matroid U}{N: matroid V}(iso : isom M N) : isom N M := 
{
  bij := iso.bij.symm,
  rank_preserving := 
  by {rw iso.rank_preserving, unfold equiv.img, ext X, convert rfl, convert rfl, ext x, simp}, 
}

def compose {M : matroid U}{N : matroid V}{O : matroid W}(i₁ : isom M N)(i₂ : isom N O): isom M O := 
{
  bij := equiv.trans i₁.bij i₂.bij, 
  rank_preserving := 
  begin
    ext X, rw [i₁.rank_preserving, i₂.rank_preserving],  
    simp only [equiv.to_fun_as_coe, ftype.ftype_coe, function.comp_app, equiv.coe_trans, equiv.img], 
    apply congr_arg, ext x,  simp, 
  end
}

-- making a hash of this one! 
@[simp] lemma compose_inv_on_set {M: matroid U}{N: matroid V}(iso : isom M N)(X : set U):
  ((inv iso).bij.img (iso.bij.img X)) = X :=
begin
  unfold equiv.img, 
  convert rfl, ext, 
  rw set.mem_image, 
  refine ⟨λ h, ⟨iso.bij x,⟨_,_⟩⟩,λ h, _⟩, 
    {simp only [equiv.to_fun_as_coe, equiv.apply_eq_iff_eq, set.mem_image, exists_eq_right], from h },
    {simp[inv]},
    {rcases h with ⟨y,h1,h2⟩, rw set.mem_image at h1, rcases h1 with ⟨x', ⟨hx'1, hx'2⟩⟩, rw [←h2,←hx'2] , convert hx'1, rw inv, simp,}
end



variable {M : matroid U}



/-- structure describing a matroid together with it having an isomorphism to a minor of M -/
structure emb_mat := 
  {U₀ : ftype}
  (mat : matroid U₀)
  (emb : U₀ ↪ U)

structure emb_minor (M : matroid U):=
  {U₀ : ftype}
  (mat : matroid U₀)
  (emb : U₀ ↪ U)
  (C : set U)
  (C_disj : C ∩ set.range emb = ∅)
  (minor_rank : mat.r = λ X, M.r (emb '' X ∪ C) - M.r C)

namespace emb_minor

/-- the ground set of an emb_minor, expressed as a set of elements of M -/
def ground (N : emb_minor M) : set U := set.range N.emb

--def C (N : emb_minor M) : set U := classical.some N.minor_rank

def D (N : emb_minor M) : set U := (N.ground ∪ N.C)ᶜ

lemma def_ground (N : emb_minor M) : N.ground = set.range N.emb  := rfl 

lemma C_ground_inter_empty (N : emb_minor M): 
  N.C ∩ N.ground = ∅ := 
by {rw ground, from N.C_disj,}

lemma D_ground_inter_empty (N : emb_minor M): 
  N.D ∩ N.ground = ∅ := 
by {rw [D], have := C_ground_inter_empty N, rw [compl_union, inter_right_comm], set_solver}
  -- set_solver doesn't work right after the have here, but it should. What's the problem? 

lemma C_D_inter_empty (N : emb_minor M) : 
  N.C ∩ N.D = ∅ := 
by {rw D, have := C_ground_inter_empty N, set_solver, } 

lemma C_union_D_eq_ground_compl (N : emb_minor M) : 
  (N.C ∪ N.D) = N.groundᶜ := 
by {rw [D], have := N.C_ground_inter_empty,rw [compl_union, union_distrib_left], simp, sorry,}
-- same deal here 

lemma emb_minor_r (N : emb_minor M)(X : set N.U₀): 
  N.mat.r X = M.r (N.emb '' X ∪ N.C) - M.r N.C := 
by rw N.minor_rank

/-- the rank function given by N when applied to a subset of the embedded ground set of N.  -/
def pullback_r (N : emb_minor M) : set (N.ground) → ℤ := 
  λ X, N.mat.r ((N.emb.subtype_inv_inj (rfl : N.ground = set.range N.emb))'' X)

/-- two embedded minors of M are strongly isomorphic if the associated matroids are related 
by an isomorphism that commutes with the respective embeddings into M. -/
def strongly_iso (N₁ N₂ : emb_minor M) : Prop := 
  (∃ (φ : isom (N₁.mat) (N₂.mat)), ∀ x, N₁.emb x = N₂.emb (φ x)) 

/-- existence of a strong isomorphism is an equivalence relation on embedded minors of M.
    Equivalence classes of this relation correspond to actual 'labelled' minors of M -/
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

/-- the ground set is an invariant of equivalence classes under strong isomorphism -/
lemma strong_iso_same_groundset (N N' : emb_minor M):
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


--variables {M : matroid U}[setoid (emb_minor_of M)]
def minor (M : matroid U) := quot (λ (N N' : emb_minor M), N.strongly_iso N')

namespace minor 

def emb_to_minor (M : matroid U) := @quotient.mk (emb_minor M) _

/-- returns the ground set of a minor of M (as a subset of the ftype for M)-/
def ground {M : matroid U} : minor M → set U := quotient.lift  
  (λ (N : emb_minor M), N.ground)
  (λ N N' hNN', emb_minor.strong_iso_same_groundset N N' hNN' )

end minor 