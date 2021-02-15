import ftype.basic ftype.induction ftype.collections .rankfun .indep 
open ftype 

local attribute [instance] classical.prop_decidable
noncomputable theory 

variables {U : ftype}

lemma basis_have_same_size (M : basis_family U) (B₁ B₂ : set U):
  M.basis B₁ → M.basis B₂ → size B₁ = size B₂ := sorry

def basis_to_indep (basis : set U → Prop) : (set U → Prop) :=
  λ I, ∃ B, basis B ∧ I ⊆ B.

def B_to_I1 (M : basis_family U) : satisfies_I1 (basis_to_indep M.basis) :=
begin
  simp only [basis_to_indep],
  have Hbasis := M.B1,
  cases M.B1 with B H,
    use B,
    split,
      assumption,
      apply empty_subset,
end

def B_to_I2 (M : basis_family U) : satisfies_I2 (basis_to_indep M.basis) :=
begin
  simp only [basis_to_indep, satisfies_I2, and_imp, exists_imp_distrib],
  intros I J HIJ B HB HindepJ,
  use B,
    split,
      assumption,
      apply subset.trans; tidy; assumption,
end

def B_to_I3 (M : basis_family U) : satisfies_I3 (basis_to_indep M.basis) :=
begin
  simp only [basis_to_indep, satisfies_I3, and_imp, exists_imp_distrib],
  intros I₁ I₂ HI₁ltI₂ B₁ HB₁ HIB₁ B₂ HB₂ HJB₂,
  
  -- B₁ = B₂ 

  have HB_case := equal_or_single_in_diff (basis_have_same_size M B₂ B₁ HB₂ HB₁),
  cases HB_case,
    {
      -- Here I and J are part of the same basis B, so we can add any element
      -- from J into_I I and still be contained in B,
      have Hb: ∃ b, b ∈ I₂ \ I₁,
      {
        -- |I| < |J|, so there is such an element.
        sorry,
      },
      cases Hb with b HbJI,
      use b, split,
        assumption,
        use B₁, split,
          assumption,
          have HIbB1 : I₁ ∪ b ⊆ B₁,
          {
            -- this is where it would be nice to_I have a tactic of sorts.
            -- split into_I I ⊆ B₁ and b ∈ B₁,
            -- first by assumption, second by b ∈ J ⊆ B₁
            sorry,
          },
          assumption,
    },
    -- B₁ <> B₂, hence there is an element e ∈ B₁ - B₂
    {
      -- so I₁  ⊆ B1,
      -- so I₂  ⊆ B2,
      have Hcase1 : (I₂ \ B₁ = I₂ \ I₁ ∨ ¬ I₂ \ B₁ = I₂ \ I₁), apply em,
      -- equal
      cases Hcase1,
      {
        have Hminimaldiff := @minimal_example U
          (fun (X : set U), 
            ∃ B : set U, M.basis B ∧ I₂ ⊆ B ∧ X = B \ (I₂ ∪ B₁))
          (B₂ \ (I₂ ∪ B₁))
          (begin
            use B₂, split,
              assumption,
              split,
                assumption,
                refl,
          end)
        ,
        simp only [not_exists, and_imp, not_and, ne.def, ssubset_iff] at Hminimaldiff,
        rcases Hminimaldiff with 
          ⟨X, ⟨_, ⟨⟨B₂', ⟨HB₂', ⟨HB₂'I₂, HX⟩⟩⟩, 
                    Hminimal⟩⟩⟩,
        -- Two cases: B₂ - (I₂ ∪ B₁) = ⊥ or not
        have Hcase2 : (B₂ \ (I₂ ∪ B₁) = ⊥ ∨ ¬ B₂ \ (I₂ ∪ B₁) = ⊥), apply em,
        cases Hcase2,
        {
          -- empty
          -- set facts
          -- B₂ - I₂ ∪ B₁ is empty,
          -- so everything in B₂ is in I₂ or in B₁,
          -- so the stuff not in B₁ (B₂ - B₁) is just
          -- I₂ - B₁, which from above (Hcase1) is I₂ - I₁
          have HB₂B₁ : B₂ \ B₁ = I₂ \ I₁ := sorry,

          -- Two cases:
          -- either B₁ - (I₁ ∪ B₂) = ⊥ or not
          have Hcase3 : (B₁ \ (I₁ ∪ B₂) = ⊥ ∨ ¬ B₁ \ (I₁ ∪ B₂) = ⊥), apply em,
          cases Hcase3,
          {
            -- empty, derive a contradiction.
            -- symmetrically, as B₁ - I₁ ∪ B₂ is empty,
            -- B₁ - B₂ = I₁ - B₂
            have HB₁B₂ : B₁ \ B₂ = I₁ \ B₂ := sorry,
            have Hsize := basis_have_same_size M B₁ B₂ HB₁ HB₂,
            -- set difference fact : |B₁| = |B₂| → |B₁ - B₂| = |B₂ - B₁| = |B_x| - |B₁ ∩ B₂|
            have Hsizeeq : size (B₁ \ B₂) = size (B₂ \ B₁) := sorry,
            -- now, as B₁ - B₂ ⊆ I₁ - B₂ ⊆ I₁ - I₂,
            -- |I₁ - I₂| ≥ |B₁ - B₂| = |B₂ - B₁| = |I₂ - I₁|,
            -- hence |I₁| ≥ |I₂|
            have : size I₁ ≥ size I₂ := sorry,
            linarith, 
          },
          {
            -- not empty, get goal.
            have Hx : (∃ x, x ∈ B₁ \ (I₁ ∪ B₂)) := sorry,
            cases Hx with x Hx,        
            -- again, tactic...
            have HB₁x : x ∈ B₁ \ B₂ := sorry,
            have := M.B2 B₁ B₂ HB₁ HB₂ x HB₁x,
            rcases this with ⟨y, ⟨_, H⟩⟩,
            use y,
            split,
              rw <- HB₂B₁, assumption,
              use (B₁ \ x) ∪ y, split,
                assumption,
                -- x ∉ I₁, so just set facts here now.
                sorry,
          }
        },
        {
          -- not empty, so there exists x it (probably a ftype axiom)
          have Hx : (∃ x, x ∈ B₂ \ (I₂ ∪ B₁)) := sorry,
          cases Hx with x Hx,
          -- nice to_I have a tactic here
          have HB₂x : x ∈ B₂ \ B₁ := sorry,
          have := M.B2 B₂ B₁ HB₂ HB₁ x HB₂x,
          rcases this with ⟨y, ⟨_, H⟩⟩,
          set Z := ((B₂ \ x) ∪ y) \ (I₂ ∪ B₁),
          -- derive contradiction of minimality
          exfalso,
          apply (Hminimal Z), -- 5 goals
            -- set facts: if x ∈ (B₂ - x) ∪ y - (I₂ ∪ B₁),
            -- then it is in B₂ - (I₂ ∪ B₁) as y is in B₁.#check
            sorry,
            -- set facts: ¬ Z = X as x ∈ X, x ∉ Z,
            sorry,
            apply H,
            -- set facts : x ∈ B₂ - I₂ ∪ B₁, so x ∉ I₂,
            -- so I₂ ⊆ B₂ - x ⊆ B₂ - x ∪ y,
            sorry,
            -- just the definition of Z,
            refl,
        }
      },
      -- not equal
      {
        -- I₂ - B₁ ≠ I₂ - I₁, as I₁ ⊆ I₂ we have b ∈ I₂ - I₁ ∩ B₁
        have Hb : (∃ e, e ∈ (I₂ \ I₁) ∩ B₁) := sorry,
        cases Hb with b Hb,
        use b,
        split,
          -- b is in the difference (want something to_I turn ∩ <-> ∧)
          sorry,
          -- 
          use B₁, split, assumption,
            -- b ∈ I₁, so we're all good.
            sorry,
      },
    },
end

