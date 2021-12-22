
import topology.homotopy.basic
import topology.constructions

noncomputable theory

namespace continuous_map.homotopy
section

parameters {α β : Type*} [topological_space α] [topological_space β]
           {A : Type*} [topological_space A]


-- product of maps
local notation f ` ×ₘ ` g :=  (continuous_map.prod_mk f g)

@[simp]
lemma biprod_eval {f : C(A, α)} {g : C(A, β)} {a : A} : (f ×ₘ g) a = (f a, g a) := rfl

def prod 
  {f f' : C(A, α)} {g g' : C(A, β)} {S : set A}
  (homotopy₁ : continuous_map.homotopy_rel f f' S)
  (homotopy₂ : continuous_map.homotopy_rel g g' S) :
  continuous_map.homotopy_rel (f ×ₘ g) (f' ×ₘ g') S :=
  { to_fun := λ t, (homotopy₁ t, homotopy₂ t),
  continuous_to_fun := by continuity,
  to_fun_zero := by { intro, simp only [biprod_eval, continuous_map.homotopy_with.apply_zero], },
  to_fun_one := by { intro, simp only [biprod_eval, continuous_map.homotopy_with.apply_one], },
  prop' :=
  begin
    intros t x hx,
    have t₁ := homotopy₁.prop' t x hx,
    have t₂ := homotopy₂.prop' t x hx,
    simp only [biprod_eval],
    rw [← t₁.1, ← t₁.2, ← t₂.1, ← t₂.2],
    split; refl,
  end }


end
end continuous_map.homotopy