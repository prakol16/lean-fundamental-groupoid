import topology.homotopy.basic

-- For some reason, projections are not solved by `continuity`
lemma pi_continuity_reverse {α : Type*} {ι : Type*} {π : ι → Type*}
          [topological_space α] [∀ i : ι, topological_space (π i)]
          (f : α → Π i, π i) (i : ι) {fc : continuous f} 
          : continuous (λ x, f x i)
          :=
by { rw continuous_pi_iff at fc, exact fc i, }

namespace continuous_map
section
parameters {I : Type*} {X : I → Type*}
           [∀i, topological_space (X i)]
           {A : Type*}
           [topological_space A]

def product (f : Π i, C(A, X i)) : C(A, Π i, X i) := 
{ to_fun := λ (a : A) (i : I), f i a,
  continuous_to_fun := by continuity, }

@[simp]
lemma product_eval (f : Π i, C(A, X i)) (a : A)  :
  (product f) a  = λ i : I, (f i) a := rfl



def projection (i : I) (f : C(A, Π i, X i)) : C(A, X i) :=
{ to_fun := λ (a : A), f a i,
  continuous_to_fun := by 
  { apply pi_continuity_reverse, exact f.continuous_to_fun, }, }

@[simp]
lemma projection_eval (i : I) (f : C(A, Π i, X i)) (a : A) :
  (projection i f) a = f a i := rfl

namespace homotopy
section
noncomputable def product_homotopy 
  (f g : Π i, C(A, X i)) (S : set A)
  (homotopies : Π i : I, continuous_map.homotopy_rel (f i) (g i) S)
  : continuous_map.homotopy_rel (product f) (product g) S :=
{ to_fun := λ t i, (homotopies i).to_fun t,
  continuous_to_fun := by continuity,
  to_fun_zero := by { 
    intro t, ext i, simpa only [(homotopies i).to_fun_zero], },
  to_fun_one := by { 
    intro t, ext i, simpa only [(homotopies i).to_fun_one], },

  prop' :=
  begin
    intros t x hx,
    have := λ i, (homotopies i).prop' t x hx,
    -- repeat {finish}, -- this works, but it's slow
    change (λ (i : I), (homotopies i) (t, x)) = (λ i, f i x) ∧
          (λ (i : I), (homotopies i) (t, x)) = (λ i, g i x),
    change ∀ i, (homotopies i) (t, x) = (f i) x ∧ (homotopies i) (t, x) = (g i) x at this,
    split;
      ext i;
      have := this i;
      tauto,
  end, }

noncomputable def proj_homotopy
  (i : I) (f g : C(A, Π i, X i))
  (S : set A)
  (homotopies : continuous_map.homotopy_rel f g S) :
  continuous_map.homotopy_rel (projection i f) (projection i g) S
  :=
{ to_fun := λ ts, (homotopies ts i),
  continuous_to_fun := by { apply pi_continuity_reverse, exact homotopies.continuous_to_fun, },
  to_fun_zero := 
  begin
    intro s,
    change homotopies (0, s) i = f s i,
    suffices : homotopies (0, s) = f s, { rw this, },
    exact homotopies.to_fun_zero s,
  end,
  to_fun_one :=
  begin
    intro s,
    change homotopies (1, s) i = g s i,
    suffices : homotopies (1, s) = g s, { rw this, },
    exact homotopies.to_fun_one s,
  end,
  prop' :=
  begin
    intros t s x,
    change homotopies (t, s) i = f s i ∧ homotopies (t, s) i = g s i,
    have := homotopies.prop' t s x,
    change homotopies (t, s) = f s ∧ homotopies (t, s) = g s at this,
    tauto,
  end }
end
end homotopy
end
end continuous_map