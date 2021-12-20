import category_theory.category.Groupoid
import category_theory.groupoid
import topology.category.Top.basic
import topology.homotopy.basic
import topology.homotopy.fundamental_groupoid
import topology.constructions
import category_theory.functor
import groupoid_products
import path_homotopy_products

noncomputable theory


section
abbreviation π := fundamental_groupoid.fundamental_groupoid_functor

parameters {I : Type*} (X : I → Top)


def pi_prod_X_to_prod_pi_X : (π.obj (Top.of (Π i, X i))).α 
  ⥤ Π i, (π.obj (X i)).α :=
{ obj := λ g, g,
  map := λ v₁ v₂ p, λ i, path.homotopic.path_proj.quotient i p,
  map_id' := by { intro x, ext i, exact path.homotopic.proj_id_is_id.quotient i x, },
  map_comp' :=
  begin
    intros x y z f g,
    ext i,
    exact path.homotopic.homproj_commutes_with_comp i f g,
  end }


def prod_pi_X_to_pi_prod_X : (Π i : I, (π.obj (X i)).α)
        ⥤ (π.obj (Top.of (Π i, X i))).α := 
{ obj := λ g, g,
  map := λ v₁ v₂ p, path.homotopic.path_prod.quotient p,
  map_id' := path.homotopic.id_product_is_id.quotient,
  map_comp' :=
  begin
    intros x y z f g,
    exact (path.homotopic.hompath_trans_commutes_with_product f g).symm,
  end }

@[simp]
lemma def_pi_prod_X_to_prod_pi_X {x y : (π.obj (Top.of (Π i, X i))).α} {f : x ⟶ y} 
  : pi_prod_X_to_prod_pi_X.map f = λ i : I, path.homotopic.path_proj.quotient i f := rfl

@[simp]
lemma def_prod_pi_X_to_pi_prod_X {x y : Π i : I, (π.obj (X i)).α}
           {f : x ⟶ y} : prod_pi_X_to_pi_prod_X.map f = path.homotopic.path_prod.quotient f := rfl 

lemma iso₁ : pi_prod_X_to_prod_pi_X ⋙ prod_pi_X_to_pi_prod_X = 𝟭 _ :=
begin
  apply category_theory.functor.ext; intros,
  { simp, }, { refl, },
end

lemma iso₂ : prod_pi_X_to_pi_prod_X ⋙ pi_prod_X_to_prod_pi_X = 𝟭 _ :=
begin
  apply category_theory.functor.ext; intros,
  { simp, }, { refl, },
end


end

