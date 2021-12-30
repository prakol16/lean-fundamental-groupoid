import category_theory.category.Groupoid
import category_theory.groupoid
import topology.category.Top.basic
import topology.homotopy.basic
import topology.homotopy.fundamental_groupoid
import topology.constructions
import category_theory.functor
import groupoid_products
import path_homotopy_products
import path_homotopy_binary_products

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
section
open category_theory
universes u₁ u₂ u₃ v₁ v₂ v₃
variables {A : Type u₁} [category.{v₁} A]
          {B : Type u₂} [category.{v₂} B]
          {C : Type u₃} [category.{v₃} C]

@[simps]
def prod' (F : A ⥤ B) (G : A ⥤ C) : A ⥤ B × C := 
{ obj := λ a, (F.obj a, G.obj a),
  map := λ x y f, (F.map f, G.map f),
  }

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
parameters {α β : Top.{u}}

def pi_proj_left : (π.obj (Top.of (α × β))).α ⥤ (π.obj α).α :=
  π.map (⟨_, continuous_fst⟩)

def pi_proj_right : (π.obj (Top.of (α × β))).α ⥤ (π.obj β).α :=
  π.map (⟨_, continuous_snd⟩)

def pi_proj : (π.obj (Top.of (α × β))).α ⥤ (π.obj α).α × (π.obj β).α :=
  pi_proj_left.prod' pi_proj_right

@[simps]
def prod_to_pi : (π.obj α).α × (π.obj β).α ⥤ (π.obj (Top.of (α × β))).α :=
{ obj := λ p, p,
  map := λ X Y (p : X ⟶ Y), path.homotopic.prod.quotient p.1 p.2,
  map_id' := λ x, path.homotopic.id_prod.quotient x.1 x.2,
  map_comp' := λ x y z f g, path.homotopic.hcomp_comm_prod f.1 f.2 g.1 g.2 }

section test
variables {x y : (π.obj (Top.of (α × β))).α} (f : x ⟶ y)
@[simp] lemma def_pi_proj_left  :
  pi_proj_left.map f = path.homotopic.proj.left.quotient f := rfl

@[simp] lemma def_pi_proj_right :
  pi_proj_right.map f = path.homotopic.proj.right.quotient f := rfl

@[simp] lemma def_pi_proj_to_left :
  (pi_proj.map f).1 = pi_proj_left.map f := rfl

@[simp] lemma def_pi_proj_to_right :
  (pi_proj.map f).2 = pi_proj_right.map f := rfl

@[simp] lemma def_pi_proj_obj : pi_proj.obj x = x := by { ext; refl, }

end test

theorem iso₃ : pi_proj ⋙ prod_to_pi = 𝟭 _ :=
begin
  apply category_theory.functor.hext, { simp, },
  intros x y f,
  simp only [category_theory.functor.id_map,
    def_pi_proj_left,
    def_pi_proj_to_left,
    category_theory.functor.comp_map,
    def_pi_proj_to_right,
    prod_to_pi_map,
    def_pi_proj_right],
  convert heq_iff_eq.mpr (path.homotopic.prod_proj.quotient' f);
   simp,
end

theorem iso₄ : prod_to_pi ⋙ pi_proj = 𝟭 _ :=
begin
  apply category_theory.functor.hext, { simp, },
  intros x y f,
  simp [prod.ext_iff],
end

end

end
