import category_theory.full_subcategory
import category_theory.groupoid
import category_theory.functor
import category_theory.endomorphism
import category_theory.is_connected

namespace category_theory.groupoid
section
open category_theory


@[simp] lemma comp_inv_x {G : Type*} [category_theory.groupoid G] {x y z : G}
                {f : x ⟶ y} {g : x ⟶ z} : f ≫ (inv f) ≫ g = g :=
by rw [← category.assoc, comp_inv, category.id_comp]

@[simp] lemma inv_comp_x {G : Type*} [category_theory.groupoid G] {x y z : G}
                {f : y ⟶ x} {g : x ⟶ z} : (inv f) ≫ f ≫ g = g :=
by rw [← category.assoc, inv_comp, category.id_comp]

end

section
lemma iso_of_groupoid_connected {G : Type*} [category_theory.groupoid G]
  (conn : category_theory.is_preconnected G) (x y : G) : nonempty (x ≅ y) :=
begin
  refine nonempty.map (category_theory.groupoid.iso_equiv_hom x y).inv_fun _,
  let x_path_component := {z : G | nonempty (x ⟶ z)},
  change y ∈ x_path_component,
  refine category_theory.induct_on_objects x_path_component (_ : x ∈ x_path_component) _ y,
  { exact nonempty.intro (𝟙 x), },
  { intros a b fab,
    split,
    { intro ha,
      exact nonempty.map (λ fxa : x ⟶ a, fxa ≫ fab) ha, },
    { intro hb,
      exact nonempty.map (λ fxb : x ⟶ b, fxb ≫ (inv fab)) hb, }
  }
end

end

section
variables {g : Type*} [category_theory.groupoid g]
            (x₁ : g) (x₂ : g)

@[reducible]
def to_group (x : g) := category_theory.End x

lemma to_group_iso (f : x₁ ⟶ x₂) : to_group x₁ ≃* to_group x₂ :=
{ to_fun := λ a, (inv f) ≫ a ≫ f,
  inv_fun := λ a, f ≫ a ≫ (inv f),
  left_inv := by { intro, simp, },
  right_inv := by { intro, simp, },
  map_mul' := by simp, }

lemma to_group_iso_connected (conn : category_theory.is_preconnected g) :
  nonempty (to_group x₁ ≃* to_group x₂) :=
begin
  refine nonempty.map (to_group_iso x₁ x₂) _,
  refine nonempty.map (category_theory.groupoid.iso_equiv_hom x₁ x₂) _,
  exact (iso_of_groupoid_connected conn x₁ x₂),
end
end

end category_theory.groupoid