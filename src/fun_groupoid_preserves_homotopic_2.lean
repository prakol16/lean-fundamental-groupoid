import fundamental_groupoid_product

noncomputable theory

variables {X : Type*} {Y : Type*} [topological_space X] [topological_space Y] {f g : C(X, Y)}
          (H : continuous_map.homotopy f g)

namespace continuous_map.homotopy

def to_path (x : X) : path (f x) (g x) :=
{ to_fun := λ t, H (t, x),
  source' := by simp only [continuous_map.homotopy.apply_zero],
  target' := by simp only [continuous_map.homotopy.apply_one], }

end continuous_map.homotopy

open_locale unit_interval

namespace path.homotopic

local attribute [instance] path.homotopic.setoid

section cast

variables {x₀ x₁ x₂ x₃ : X}

protected def cast (p₀ : x₀ = x₁) (p₁ : x₂ = x₃) (P : path.homotopic.quotient x₁ x₃) : 
  (path.homotopic.quotient x₀ x₂) := by rwa [p₀, p₁]

@[simp] lemma cast_of_eq (P : path.homotopic.quotient x₀ x₁) : path.homotopic.cast rfl rfl P = P := rfl 

lemma cast_lift (p₀ : x₀ = x₁) (p₁ : x₂ = x₃) (P₀ : path x₁ x₃) : ⟦P₀.cast p₀ p₁⟧ = path.homotopic.cast p₀ p₁ ⟦P₀⟧ := 
by { subst_vars, rw cast_of_eq, congr, ext, rw path.cast_coe, }

lemma path_heq_cast (p₀ : x₀ = x₁) (p₁ : x₂ = x₃) (P : path x₁ x₃) : P.cast p₀ p₁ == P :=
by { subst_vars, rw heq_iff_eq, ext, rw path.cast_coe, }

lemma path.homotopic.heq_cast (p₀ : x₀ = x₁) (p₁ : x₂ = x₃) (P : path.homotopic.quotient x₁ x₃) : 
path.homotopic.cast p₀ p₁ P == P := by { subst_vars, refl, }

end cast

variables (x₀ x₁ : X) (p : path.homotopic.quotient x₀ x₁)

def straight_path : path (0 : I) (1 : I) := { to_fun := id, source' := rfl, target' := rfl }

def diagonal_path : path.homotopic.quotient (H (0, x₀)) (H (1, x₁)) :=
(path.homotopic.prod ⟦straight_path⟧ p).map_fn H.to_continuous_map

def diagonal_path' : path.homotopic.quotient (f x₀) (g x₁) :=  
path.homotopic.cast (H.apply_zero x₀).symm (H.apply_one x₁).symm (diagonal_path H x₀ x₁ p)

lemma up_is_f : (p.map_fn f) = path.homotopic.cast (H.apply_zero x₀).symm (H.apply_zero x₁).symm ((path.homotopic.prod ⟦path.refl (0 : I)⟧ p).map_fn H.to_continuous_map) :=
begin
  apply quotient.induction_on p,
  intro p',
  rw [path.homotopic.prod_lift, ← path.homotopic.map_lift, ← path.homotopic.map_lift, ← cast_lift],
  congr, ext, simp,
end

lemma down_is_g : p.map_fn g = path.homotopic.cast (H.apply_one x₀).symm (H.apply_one x₁).symm ((path.homotopic.prod ⟦path.refl (1 : I)⟧ p).map_fn H.to_continuous_map) :=
begin
  apply quotient.induction_on p,
  intro p',
  rw [path.homotopic.prod_lift, ← path.homotopic.map_lift, ← path.homotopic.map_lift, ← cast_lift],
  congr, ext, simp,
end

lemma H_to_path (x : X) : ⟦H.to_path x⟧ =
  path.homotopic.cast (H.apply_zero x).symm (H.apply_one x).symm ((path.homotopic.prod ⟦straight_path⟧ ⟦path.refl x⟧).map_fn H.to_continuous_map) :=
by { rw [prod_lift, ← map_lift, ← cast_lift], refl, }

lemma up_right_is_diag : (p.map_fn f).comp ⟦H.to_path x₁⟧ = diagonal_path' H x₀ x₁ p :=
begin
  rw up_is_f H x₀ x₁ p,
  sorry,
end 

end path.homotopic