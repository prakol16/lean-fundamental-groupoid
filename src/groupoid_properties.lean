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

@[simp] lemma mul_def_Aut {C : Type*} [category_theory.category C] {x : C} (a b : category_theory.Aut x) :
  a * b = b.trans a := rfl

end

section

lemma groupoid_connected_of_homs {G : Type*} [category_theory.groupoid G]
  [nonempty G] (iso : ∀ (x y : G), nonempty (x ⟶ y)) : category_theory.is_connected G :=
  category_theory.zigzag_is_connected (λ j₁ j₂, relation.refl_trans_gen.single 
    (or.inl (iso j₁ j₂)))

lemma groupoid_connected_iff_hom {G : Type*} [category_theory.groupoid G] [nonempty G] :
  category_theory.is_connected G ↔ ∀ (x y : G), nonempty (x ⟶ y) :=
⟨λ conn, @category_theory.nonempty_hom_of_connected_groupoid G _ conn, groupoid_connected_of_homs⟩

lemma groupoid_connected_iff_iso {G : Type*} [category_theory.groupoid G] [nonempty G] :
  category_theory.is_connected G ↔ ∀ (x y : G), nonempty (x ≅ y) :=
begin
  simp_rw (λ (x y : G), equiv.nonempty_congr (category_theory.groupoid.iso_equiv_hom x y)),
  exact groupoid_connected_iff_hom,
end

end

section
variables {g : Type*} [category_theory.groupoid g]
            (x₁ : g) (x₂ : g)
          {C : Type*} [category_theory.category C]
            {y₁ y₂ : C}

@[reducible]
def to_group (x : g) := category_theory.End x

def iso_induces_iso_of_Aut (f : y₁ ≅ y₂) : category_theory.Aut y₁ ≃* category_theory.Aut y₂ :=
{ to_fun := λ a, { hom := f.inv ≫ a.hom ≫ f.hom,
                   inv := f.inv ≫ a.inv ≫ f.hom,
                   hom_inv_id' := by simp, inv_hom_id' := by simp },
  inv_fun := λ a, { hom := f.hom ≫ a.hom ≫ f.inv,
                    inv := f.hom ≫ a.inv ≫ f.inv,
                    hom_inv_id' := by simp,
                    inv_hom_id' := by simp, },
  left_inv := by { intro, ext, simp, },
  right_inv := by { intro, ext, simp, },
  map_mul' := by { intros, ext, simp, } }


def to_group_is_Aut (x : g) : category_theory.Aut x ≃* to_group x :=
{ map_mul' := λ a b, rfl
  ..(category_theory.groupoid.iso_equiv_hom x x) }

def to_group_iso (f : x₁ ⟶ x₂) : to_group x₁ ≃* to_group x₂ := 
  ((to_group_is_Aut x₁).symm.trans
  (iso_induces_iso_of_Aut ((category_theory.groupoid.iso_equiv_hom x₁ x₂).inv_fun f))).trans
  (to_group_is_Aut x₂)

lemma to_group_iso_to_fun (f : x₁ ⟶ x₂) : (to_group_iso x₁ x₂ f).to_fun = λ a, (inv f) ≫ a ≫ f := rfl
lemma to_group_iso_inv_fun (f : x₁ ⟶ x₂) : (to_group_iso x₁ x₂ f).inv_fun = λ a, f ≫ a ≫ (inv f) := rfl

lemma to_group_iso_connected [category_theory.is_connected g] :
  nonempty (to_group x₁ ≃* to_group x₂) := nonempty.map (to_group_iso x₁ x₂) (category_theory.nonempty_hom_of_connected_groupoid x₁ x₂)


lemma nat_iso_of_groupoid_nat_trans {h : Type*} [category_theory.groupoid h] {a b : g ⥤ h} (nt : a ⟶ b) :
  category_theory.is_iso nt := category_theory.nat_iso.is_iso_of_is_iso_app nt

end

end category_theory.groupoid