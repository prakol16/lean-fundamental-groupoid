
import topology.homotopy.basic
import topology.constructions
import topology.homotopy.path
import category_theory.groupoid
import groupoid_products
import topology.homotopy.fundamental_groupoid
import topology.homotopy.product

noncomputable theory

namespace fundamental_groupoid


private abbreviation π := fundamental_groupoid_functor
universes u

section pi

variables {I : Type u} {X : I → Top.{u}}

/--
The projection map Π i, X i → X i induces a map π(Π i, X i) ⟶ π(X i).
-/
def proj (i : I) : (π.obj (Top.of (Π i, X i))).α ⥤ (π.obj (X i)).α := π.map ⟨_, continuous_apply i⟩

/-- The projection map is precisely path.homotopic.proj interpreted as a functor -/
@[simp] lemma proj_map (i : I) (x₀ x₁ : (π.obj (Top.of (Π i, X i))).α) (p : x₀ ⟶ x₁) :
  (proj i).map p = (@path.homotopic.proj _ _ _ _ _ i p) := rfl

/--
The map taking the pi product of a family of fundamental groupoids to the fundamental
groupoid of the pi product. This is actually an isomorphism (see `pi_fgrpd_iso_fgrpd_pi`)
-/
@[simps]
def pi_fgrpd_to_fgrpd_pi :
  (Π i, (π.obj (X i)).α) ⥤ (π.obj (Top.of (Π i, X i))).α :=
{ obj := λ g, g,
  map := λ v₁ v₂ p, path.homotopic.pi p,
  map_id' :=
  begin
    intro x,
    change path.homotopic.pi (λ i, 𝟙 (x i)) = _,
    simp only [id_eq_path_refl, path.homotopic.pi_lift],
    refl,
  end,
  map_comp' := λ x y z f g, (path.homotopic.comp_pi_eq_pi_comp f g).symm, }

/--
Shows `pi_fgrpd_to_fgrpd_pi` is an isomorphism, whose inverse is precisely the pi product
of the induced projections. This shows that `fundamental_groupoid_functor` preserves products.
-/
@[simps]
def pi_fgrpd_iso_fgrpd_pi :
  category_theory.Groupoid.of (Π i : I, (π.obj (X i)).α) ≅ (π.obj (Top.of (Π i, X i))) :=
{ hom := pi_fgrpd_to_fgrpd_pi,
  inv := category_theory.functor.pi' proj,
  hom_inv_id' :=
  begin
    change pi_fgrpd_to_fgrpd_pi ⋙ (category_theory.functor.pi' proj) = 𝟭 _,
    apply category_theory.functor.ext; intros,
    { ext, simp, }, { refl, },
  end,
  inv_hom_id' :=
  begin
    change (category_theory.functor.pi' proj) ⋙ pi_fgrpd_to_fgrpd_pi = 𝟭 _,
    apply category_theory.functor.ext; intros,
    { suffices : path.homotopic.pi ((category_theory.functor.pi' proj).map f) = f, { simpa, },
      change (category_theory.functor.pi' proj).map f
        with λ i, (category_theory.functor.pi' proj).map f i,
      simp, }, { refl, }
  end }

end pi

section prod

variables {A B : Top.{u}}

/-- The induced map of the left projection map X × Y → X -/
def proj_left : (π.obj (Top.of (A × B))).α ⥤ (π.obj A).α := π.map ⟨_, continuous_fst⟩

/-- The induced map of the right projection map X × Y → Y -/
def proj_right : (π.obj (Top.of (A × B))).α ⥤ (π.obj B).α := π.map ⟨_, continuous_snd⟩

@[simp] lemma proj_left_map (x₀ x₁ : (π.obj (Top.of (A × B))).α) (p : x₀ ⟶ x₁) :
  proj_left.map p = path.homotopic.proj_left p := rfl

@[simp] lemma proj_right_map (x₀ x₁ : (π.obj (Top.of (A × B))).α) (p : x₀ ⟶ x₁) :
  proj_right.map p = path.homotopic.proj_right p := rfl


/--
The map taking the product of two fundamental groupoids to the fundamental groupoid of the product
of the two topological spaces. This is in fact an isomorphism (see `prod_fgrpd_iso_fgrpd_prod`).
-/
@[simps]
def prod_fgrpd_to_fgrpd_prod : (π.obj A).α × (π.obj B).α ⥤ (π.obj (Top.of (A × B))).α :=
{ obj := λ g, g,
  map := λ x y p, match x, y, p with
    | (x₀, x₁), (y₀, y₁), (p₀, p₁) := path.homotopic.prod p₀ p₁
  end,
  map_id' :=
  begin
    rintro ⟨x₀, x₁⟩,
    simp only [category_theory.prod_id, id_eq_path_refl],
    unfold_aux, rw path.homotopic.prod_lift, refl,
  end,
  map_comp' := λ x y z f g, match x, y, z, f, g with
    | (x₀, x₁), (y₀, y₁), (z₀, z₁), (f₀, f₁), (g₀, g₁) :=
    (path.homotopic.comp_prod_eq_prod_comp f₀ f₁ g₀ g₁).symm
  end }

/--
Shows `prod_fgrpd_to_fgrpd_prod` is an isomorphism, whose inverse is precisely the product
of the induced left and right projections.
-/
@[simps]
def prod_fgrpd_iso_fgrpd_prod :
  category_theory.Groupoid.of ((π.obj A).α × (π.obj B).α) ≅ (π.obj (Top.of (A × B))) :=
{ hom := prod_fgrpd_to_fgrpd_prod,
  inv := proj_left.prod' proj_right,
  hom_inv_id' :=
  begin
    change prod_fgrpd_to_fgrpd_prod ⋙ (proj_left.prod' proj_right) = 𝟭 _,
    apply category_theory.functor.hext, { intros, ext; simp; refl, },
    rintros ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ ⟨f₀, f₁⟩,
    have := and.intro (path.homotopic.proj_left_prod f₀ f₁) (path.homotopic.proj_right_prod f₀ f₁),
    simpa,
  end,
  inv_hom_id' :=
  begin
    change (proj_left.prod' proj_right) ⋙ prod_fgrpd_to_fgrpd_prod = 𝟭 _,
    apply category_theory.functor.hext, { intros, ext; simp; refl, },
    rintros ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ f,
    have := path.homotopic.prod_proj_left_proj_right f,
    simpa,
  end }

end prod

end fundamental_groupoid