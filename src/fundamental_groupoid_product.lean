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

/-
 - Given a family of topological spaces `X` indexed by `I`,
   we show that π (Πᵢ Xᵢ) = Πᵢ (π Xᵢ)
 - This isomorphism is given by two homomorphisms (note that
    homomorphisms between groupoids are functors):
    - `pi_prod_X_to_prod_pi_X` which is a map π (Πᵢ Xᵢ) ⥤ Πᵢ (π Xᵢ)
    - `prod_pi_X_to_pi_prod_X` which is a map Πᵢ (π Xᵢ) ⥤ π (Πᵢ Xᵢ)
 - We prove the theorems `iso₁` and `iso₂` which show that these
   really are inverses of each others.
 - TODO: It should also be straightforward to show that
         pi_prod_X_to_prod_pi_X preserves projections
         i.e. a projection projᵢ = Πᵢ Xᵢ → Xᵢ
         maps under π to the corresponding ith projection
         Πᵢ πXᵢ → πXᵢ. This should be mostly just 
         unrolling definitions and using `simp`
 -/

namespace category_theory.functor
section
open category_theory

universes w v u

@[simps]
def pi' {I : Type w} {X : I → Type u} [∀i : I, category.{v} (X i)]
        {A : Type u} [category.{v} A] (f : Π i, A ⥤ X i) :
        A ⥤ Π i, X i := 
{ obj := λ a i, (f i).obj a,
  map := λ a₁ a₂ h i, (f i).map h, }

@[simps]
def diag {I : Type w} {A : Type u} [category.{v} A] : A ⥤ (Π i : I, A) := pi' (λ i, 𝟭 A)

lemma pi'_diag_pi 
        {I : Type w} {X : I → Type u} [∀i : I, category.{v} (X i)]
        {A : Type u} [category.{v} A] {f : Π i, A ⥤ X i} :
        pi' f = diag ⋙ functor.pi f := by obviously

end
end category_theory.functor


section
universe u
abbreviation π := fundamental_groupoid.fundamental_groupoid_functor

parameters {I : Type u} (X : I → Top.{u})

def pi_prod_X_to_prod_pi_X_i (i : I) : (π.obj (Top.of (Π i, X i))).α 
  ⥤ (π.obj (X i)).α :=
  π.map (to_bundled (continuous_apply i))


def pi_prod_X_to_prod_pi_X : (π.obj (Top.of (Π i, X i))).α 
  ⥤ Π i, (π.obj (X i)).α := (category_theory.functor.pi' pi_prod_X_to_prod_pi_X_i)

def prod_pi_X_to_pi_prod_X : (Π i : I, (π.obj (X i)).α)
        ⥤ (π.obj (Top.of (Π i, X i))).α := 
{ obj := λ g, g,
  map := λ v₁ v₂ p, path.homotopic.path_prod.quotient p,
  map_id' := path.homotopic.id_product_is_id.quotient,
  map_comp' := λ x y z f g, (path.homotopic.hompath_trans_commutes_with_product f g).symm }

@[simp]
lemma def_pi_prod_X_to_prod_pi_X {x y : (π.obj (Top.of (Π i, X i))).α} {f : x ⟶ y} 
  : pi_prod_X_to_prod_pi_X.map f = λ i : I, path.homotopic.path_proj.quotient i f := rfl

@[simp]
lemma def_prod_pi_X_to_pi_prod_X {x y : Π i : I, (π.obj (X i)).α}
           {f : x ⟶ y} : prod_pi_X_to_pi_prod_X.map f = path.homotopic.path_prod.quotient f := rfl 

theorem iso₁ : pi_prod_X_to_prod_pi_X ⋙ prod_pi_X_to_pi_prod_X = 𝟭 _ :=
begin
  apply category_theory.functor.ext; intros,
  { simp, }, { refl, },
end

theorem iso₂ : prod_pi_X_to_pi_prod_X ⋙ pi_prod_X_to_prod_pi_X = 𝟭 _ :=
begin
  apply category_theory.functor.ext; intros,
  { simp, }, { refl, },
end

section
parameter (i : I)

def proj_i : C(Top.of (Π i, X i), X i) := 
  to_bundled (continuous_apply i) 

def proj_i' : (Π i : I, (π.obj (X i)).α) ⥤ (π.obj (X i)).α :=
  category_theory.pi.eval _ i

theorem preserves_products : π.map proj_i = pi_prod_X_to_prod_pi_X ⋙ proj_i' := by obviously
end
end
