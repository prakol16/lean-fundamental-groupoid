import fundamental_groupoid_product

noncomputable theory

namespace continuous_map.homotopy

variables {X : Type*} {Y : Type*} [topological_space X] [topological_space Y] {f g : C(X, Y)}
          (H : continuous_map.homotopy f g)

def to_path (x : X) : path (f x) (g x) :=
{ to_fun := λ t, H (t, x),
  source' := H.apply_zero x,
  target' := H.apply_one x, }

end continuous_map.homotopy

namespace fundamental_groupoid

local attribute [reducible] fundamental_groupoid

/-- Help the typechecker by converting point in groupoid back to point in Top -/
@[reducible]
def to_top {X : Top} (x : (fundamental_groupoid_functor.obj X).α) : X := x

/-- Help the typechecker by converting point in Top to a point in the fundamental groupoid -/
@[reducible]
def from_top {X : Top} (x : X) : (fundamental_groupoid_functor.obj X).α := x

/-- Help the typechecker by converting a path in groupoid back to path.homotopic.quotient -/
@[reducible]
def to_path {X : Top} {x₀ x₁ : (fundamental_groupoid_functor.obj X).α} (p : x₀ ⟶ x₁) :
  path.homotopic.quotient x₀ x₁ := p

/-- Help the typechecker by convering a path.homotopic.quotient to an arrow in the
    fundamental groupoid -/
@[reducible]
def from_path {X : Top} {x₀ x₁ : X} (p : path.homotopic.quotient x₀ x₁) : (x₀ ⟶ x₁) := p

lemma map_map_eq {X Y : Top} {x₀ x₁ : X} (f : C(X, Y)) (p : path.homotopic.quotient x₀ x₁) :
  (fundamental_groupoid_functor.map f).map p = p.map_fn f := rfl
 

end fundamental_groupoid


section
open fundamental_groupoid
private abbreviation π := fundamental_groupoid_functor

open_locale unit_interval
local attribute [instance] path.homotopic.setoid
universes u v
section

lemma path_cast_left {X : Top} {x₀ x₁ x₀' : X} (p : path x₀ x₁) (hx₀ : x₀ = x₀') :
  (category_theory.eq_to_hom hx₀.symm : (from_top x₀') ⟶ x₀) ≫ ⟦p⟧ = ⟦p.cast hx₀.symm rfl⟧ :=
by { subst hx₀, simp only [category_theory.category.id_comp, category_theory.eq_to_hom_refl],
  congr, ext, simp, }

lemma path_cast_right {X : Top} {x₀ x₁ x₁' : X} (p : path x₀ x₁) (hx₁ : x₁ = x₁') :
  ((⟦p⟧ ≫ (category_theory.eq_to_hom hx₁ : (from_top x₁) ⟶ x₁')) : from_top x₀ ⟶ x₁') = ⟦p.cast rfl hx₁.symm⟧ :=
by { subst hx₁, simp only [category_theory.category.comp_id, category_theory.eq_to_hom_refl],
  congr, ext, simp, }

parameters {X₁ X₂ Y : Top.{u}} (f : C(X₁, Y)) (g : C(X₂, Y)) 
  {x₀ x₁ : X₁} {x₂ x₃ : X₂} (p : path x₀ x₁) (q : path x₂ x₃) (hfg : ∀ t : I, f (p t) = g (q t))

include hfg
private lemma start_path : f x₀ = g x₂ := by { convert hfg 0; simp only [path.source], }
private lemma end_path : f x₁ = g x₃ := by { convert hfg 1; simp only [path.target], }

lemma function_image_of_path  :
  (π.map f).map ⟦p⟧ = category_theory.eq_to_hom start_path ≫ (π.map g).map ⟦q⟧ ≫ category_theory.eq_to_hom end_path.symm :=
begin
  simp only [map_map_eq, ← path.homotopic.map_lift, path_cast_right],
  rw path_cast_left _ (start_path f g p q hfg).symm,
  congr, ext, simp only [path.map_coe, hfg, function.comp_app, path.cast_coe],
end

end

parameters {X : Top.{u}} {Y : Top.{u}} {f g : C(X, Y)} (H : continuous_map.homotopy f g)
variables {x₀ x₁ : X} (p : path.homotopic.quotient x₀ x₁)

def straight_path : path (0 : I) (1 : I) := { to_fun := id, source' := rfl, target' := rfl }

def diagonal_path : from_top (H (0, x₀)) ⟶ from_top (H (1, x₁)) :=
(path.homotopic.prod ⟦straight_path⟧ p).map_fn H.to_continuous_map

def diagonal_path' : from_top (f x₀) ⟶ from_top (g x₁) :=
(category_theory.eq_to_hom (H.apply_zero x₀).symm) ≫ 
  (diagonal_path p) ≫ 
  (category_theory.eq_to_hom (H.apply_one x₁))

abbreviation H_map : C(Top.of (I × X), Y) := H.to_continuous_map

lemma up_is_f : (π.map f).map p = (category_theory.eq_to_hom (H.apply_zero x₀).symm) 
  ≫ ((π.map H_map).map (path.homotopic.prod ⟦path.refl (0 : I)⟧ p)) 
  ≫ (category_theory.eq_to_hom (H.apply_zero x₁)) :=
begin
  apply quotient.induction_on p,
  intro p',
  rw path.homotopic.prod_lift,
  apply function_image_of_path f H_map,
  simp,
end

lemma down_is_g : (π.map g).map p = (category_theory.eq_to_hom (H.apply_one x₀).symm)
  ≫ ((π.map H_map).map (path.homotopic.prod ⟦path.refl (1 : I)⟧ p))
  ≫ (category_theory.eq_to_hom (H.apply_one x₁)) :=
begin
  apply quotient.induction_on p,
  intro p',
  rw path.homotopic.prod_lift,
  apply function_image_of_path g H_map,
  simp,
end

lemma H_to_path (x : X) : ⟦H.to_path x⟧ =
  (category_theory.eq_to_hom (H.apply_zero x).symm : from_top (f x) ⟶ H (0, x)) ≫
  (π.map H_map).map (path.homotopic.prod ⟦straight_path⟧ ⟦path.refl x⟧) ≫
  (category_theory.eq_to_hom (H.apply_one x)) :=
by { rw path.homotopic.prod_lift, simp only [map_map_eq, ← path.homotopic.map_lift, path_cast_left, path_cast_right], refl, }

lemma eq_diag :
  (π.map f).map p ≫ ⟦H.to_path x₁⟧ = diagonal_path' p ∧
  (⟦H.to_path x₀⟧ ≫ (π.map g).map p : from_top (f x₀) ⟶ from_top (g x₁)) = diagonal_path' p :=
begin
  rw [up_is_f, down_is_g, H_to_path, H_to_path],
  split;
  simp only [category_theory.category.id_comp, category_theory.eq_to_hom_refl,
    category_theory.category.assoc, category_theory.eq_to_hom_trans_assoc,
    ← category_theory.functor.map_comp_assoc];
  simp only [comp_eq, path.homotopic.comp_prod_eq_prod_comp];
  simp [← comp_eq, ← id_eq_path_refl]; refl,
end

def homotopic_maps_equivalent : category_theory.nat_trans (π.map f) (π.map g) :=
{ app := λ x, ⟦H.to_path x⟧,
  naturality' := by { intros x y p, rw [(eq_diag p).1, (eq_diag p).2],  } }

end