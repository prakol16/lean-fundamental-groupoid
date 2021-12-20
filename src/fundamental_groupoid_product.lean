import category_theory.category.Groupoid
import category_theory.groupoid
import topology.category.Top.basic
import topology.homotopy.basic
import topology.homotopy.fundamental_groupoid
import topology.constructions
import category_theory.functor
import category_theory.natural_isomorphism
import groupoid_products
import topology.path_connected
import path_homotopy_products

noncomputable theory

abbreviation π := fundamental_groupoid.fundamental_groupoid_functor

-- Two objects of a groupoid in same component are isomorphic

-- π (X × Y) = π X × π Y
section
universe u

parameters {I : Type u} (X : I → Top.{u})


def pi_prod_X_to_prod_pi_X : (π.obj (Top.of (Π i, X i))).α 
  ⥤ Π i, (π.obj (X i)).α :=
{
  obj := λ g, g,
  map := λ v₁ v₂ p, λ i, homotopy.product.path_proj.quotient i p,
  map_id' := by { intro x, ext i, exact homotopy.product.proj_id_is_id.quotient i x, },
  map_comp' :=
  begin
    intros x y z f g,
    ext i,
    exact homotopy.product.homproj_commutes_with_comp i f g,
  end
}


def prod_pi_X_to_pi_prod_X : (Π i : I, (π.obj (X i)).α)
        ⥤ (π.obj (Top.of (Π i, X i))).α := 
{
  obj := λ g, g,
  map := λ v₁ v₂ p, homotopy.product.path_prod.quotient p,
  map_id' := homotopy.product.id_product_is_id.quotient,
  map_comp' :=
  begin
    intros x y z f g,
    exact (homotopy.product.hompath_trans_commutes_with_product f g).symm,
  end
}

@[simp]
lemma def_pi_prod_X_to_prod_pi_X {x y : (π.obj (Top.of (Π i, X i))).α} {f : x ⟶ y} 
  : pi_prod_X_to_prod_pi_X.map f = λ i : I, homotopy.product.path_proj.quotient i f := rfl

@[simp]
lemma def_prod_pi_X_to_pi_prod_X {x y : Π i : I, (π.obj (X i)).α}
           {f : x ⟶ y} : prod_pi_X_to_pi_prod_X.map f = homotopy.product.path_prod.quotient f := rfl 

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

