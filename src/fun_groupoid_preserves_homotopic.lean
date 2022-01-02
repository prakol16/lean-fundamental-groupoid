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
import fundamental_groupoid_product
import category_theory.currying
import category_theory.eq_to_hom
import category_theory.isomorphism
import groupoid_properties

noncomputable theory

section
variables {X : Type*} {Y : Type*} [topological_space X] [topological_space Y]
variables {x₀ x₁ x₂ x₃ : X}

local attribute [instance] path.homotopic.setoid

def map_fn (P₀ : path.homotopic.quotient x₀ x₁) (f : C(X, Y)) :
                  path.homotopic.quotient (f x₀) (f x₁) := quotient.map
      (λ (q : path x₀ x₁), q.map f.continuous) (λ p₀ p₁ h, path.homotopic.map h f) P₀

lemma map_lift (P₀ : path x₀ x₁) (f : C(X, Y)) :
  ⟦P₀.map f.continuous⟧ = map_fn ⟦P₀⟧ f := rfl

def comp (P₀ : path.homotopic.quotient x₀ x₁) (P₁ : path.homotopic.quotient x₁ x₂) :
                  path.homotopic.quotient x₀ x₂ :=
                  quotient.map₂ path.trans
                  (λ (p₀ : path x₀ x₁) p₁ hp (q₀ : path x₁ x₂) q₁ hq, (path.homotopic.hcomp hp hq)) P₀ P₁

lemma comp_lift (P₀ : path x₀ x₁) (P₁ : path x₁ x₂) : ⟦P₀.trans P₁⟧ = comp ⟦P₀⟧ ⟦P₁⟧ := rfl


lemma pi_map_def {X Y : Top} (f : C(X, Y)) : (π.map f).map = λ x y p, map_fn p f := rfl

lemma comp_eq {X : Top} (x y z : fundamental_groupoid X) (p : x ⟶ y) (q : y ⟶ z) :
  p ≫ q = comp p q := rfl

def eq_to_path (p : x₀ = x₁) : path x₀ x₁ := by rw p

def path.homotopic.cast (p₀ : x₀ = x₁) (p₁ : x₂ = x₃) (P : path.homotopic.quotient x₁ x₃) : 
  (path.homotopic.quotient x₀ x₂) := by rwa [p₀, p₁]

def path_cast (p₀ : x₀ = x₁) (p₁ : x₂ = x₃) (P : path x₁ x₃) : path x₀ x₂ := by rwa [p₀, p₁]

lemma cast_lift (p₀ : x₀ = x₁) (p₁ : x₂ = x₃) (P₀ : path x₁ x₃) : ⟦P₀.cast p₀ p₁⟧ = path.homotopic.cast p₀ p₁ ⟦P₀⟧ := 
by { subst_vars, refl, }

lemma path_heq_cast (p₀ : x₀ = x₁) (p₁ : x₂ = x₃) (P : path x₁ x₃) : P.cast p₀ p₁ == P :=
by { subst_vars, refl, }

lemma path.homotopic.heq_cast (p₀ : x₀ = x₁) (p₁ : x₂ = x₃) (P : path.homotopic.quotient x₁ x₃) : 
path.homotopic.cast p₀ p₁ P == P := by { subst_vars, refl, }


#check path.cast

end

-- If f g : X → Y are maps with f ≃ g, then πf ≃ πg


section
universe u


def f_to_g {A B : Type u} [category_theory.category A] [category_theory.category B]
            {I : Type u} [category_theory.category I]
            [has_zero I] [has_one I] (i01 : (0 : I) ⟶ 1)
            (F : I × A ⥤ B)
            (f g : A ⥤ B)
            (F_zero : (category_theory.curry.obj F).obj 0 = f)
            (F_one : (category_theory.curry.obj F).obj 1 = g) :
            category_theory.nat_trans f g :=
{ app :=
begin
  intro x,
  rw [← F_zero, ← F_one],
  exact (F.map (i01, 𝟙 _)),
end,
  naturality' :=
begin
  intros x y h,
  subst F_zero,
  subst F_one,
  simp,
end }


def f_to_g' {A B : Type u} [category_theory.category A] [category_theory.category B]
            {I : Type u} [category_theory.category I]
            [has_zero I] [has_one I] (i01 : (0 : I) ⟶ 1)
            (F : I × A ⥤ B)
            (f g : A ⥤ B)
            (F_zero : (category_theory.curry.obj F).obj 0 ≅ f)
            (F_one : (category_theory.curry.obj F).obj 1 ≅ g) :
            category_theory.nat_trans f g :=
{ app := λ x, (F_zero.inv.app x : f.obj x ⟶ F.obj (0, x))
            ≫ (F.map (i01, 𝟙 x) : F.obj (0, x) ⟶ F.obj (1, x))
            ≫ (F_one.hom.app x : F.obj (1, x) ⟶ g.obj x),
  naturality' :=
begin
  intros x y p,
  rw [
    ← (category_theory.nat_iso.naturality_1 F_zero p),
    ← (category_theory.nat_iso.naturality_1 F_one p)
  ],
  -- cancel_nat_iso_hom_right_assoc is a simp lemma, but for some reason Lean doesn't get it
  have := category_theory.nat_iso.cancel_nat_iso_hom_right_assoc F_one (F.map (𝟙 0, p) : F.obj (0, x) ⟶ F.obj (0, y)) (F.map (i01, 𝟙 y)) (F.map (i01, 𝟙 x) : F.obj (0, x) ⟶ F.obj (1, x)) (F.map (𝟙 1, p)),
  simp [this],
end }

end

open_locale unit_interval
section
local attribute [instance] path.homotopic.setoid
universe u
parameters (X Y : Top.{0}) (f g : C(X, Y))
           (F : continuous_map.homotopy f g)

def F_star : (π.obj (Top.of (I × X))).α ⥤ (π.obj Y).α := π.map F.to_continuous_map
def F_star' : (π.obj (Top.of I)).α × (π.obj X).α ⥤ (π.obj Y).α := prod_to_pi ⋙ F_star

instance : has_zero ((π.obj (Top.of I)).α) := { zero := (0 : I) }
instance : has_one ((π.obj (Top.of I)).α) := { one := (1 : I) }


section test_again

local notation p₁ ` ⬝ ` p₂ := comp p₁ p₂
parameters {x₀ x₁ : X} (h : path.homotopic.quotient x₀ x₁)


lemma F_star_apply_zero :
map_fn (@path.homotopic.prod.quotient (Top.of I) X ((0 : I), x₀) ((0 : I), x₁) ⟦path.refl 0⟧ h) F.to_continuous_map 
= path.homotopic.cast (F.apply_zero x₀) (F.apply_zero x₁) (map_fn h f) :=
begin
  apply quotient.induction_on h,
  intro h',
  rw [path.homotopic.prod.quotient_rec, ← map_lift, ← map_lift, ← cast_lift],
  congr,
  ext t,
  unfold path.homotopic.prod, unfold path.refl, unfold continuous_map.prod_mk,
  simp,
end

lemma F_star_apply_one :
map_fn (@path.homotopic.prod.quotient (Top.of I) X ((1 : I), x₀) ((1 : I), x₁) ⟦path.refl 1⟧ h) F.to_continuous_map 
= path.homotopic.cast (F.apply_one x₀) (F.apply_one x₁) (map_fn h g) :=
begin
  apply quotient.induction_on h,
  intro h',
  rw [path.homotopic.prod.quotient_rec, ← map_lift, ← map_lift, ← cast_lift],
  congr,
  ext t,
  unfold path.homotopic.prod, unfold path.refl, unfold continuous_map.prod_mk,
  simp,
end


lemma F_star_apply_zero_heq :
map_fn (@path.homotopic.prod.quotient (Top.of I) X ((0 : I), x₀) ((0 : I), x₁) ⟦path.refl 0⟧ h) F.to_continuous_map
== map_fn h f :=
begin
  rw F_star_apply_zero,
  apply path.homotopic.heq_cast,
end

lemma F_star_apply_one_heq :
map_fn (@path.homotopic.prod.quotient (Top.of I) X ((1 : I), x₀) ((1 : I), x₁) ⟦path.refl 1⟧ h) F.to_continuous_map 
== map_fn h g :=
begin
  rw F_star_apply_one,
  apply path.homotopic.heq_cast,
end

end test_again

def zero_to_one_path : path (0 : I) (1 : I) := 
{ to_fun := λ t, t,
  source' := rfl,
  target' := rfl }
def zero_to_one : (0 : (π.obj (Top.of I)).α) ⟶ 1 := ⟦zero_to_one_path⟧

include F
theorem homotopic_maps_equivalent : category_theory.nat_trans (π.map f) (π.map g) :=
begin
  apply f_to_g zero_to_one F_star',
  {
    apply category_theory.functor.hext,
    { exact F.apply_zero, },
    { intros x y h, apply F_star_apply_zero_heq, }
  },
  {
    apply category_theory.functor.hext,
    { exact F.apply_one, },
    { intros, apply F_star_apply_one_heq, } 
  },
end

theorem homotopic_maps_isomorphic : π.map f ≅ π.map g :=
begin
  apply category_theory.as_iso (_ : (π.map f) ⟶ (π.map g)),
  { exact homotopic_maps_equivalent },
  apply category_theory.groupoid.nat_iso_of_groupoid_nat_trans,
end

end
