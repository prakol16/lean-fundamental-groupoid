import topology.homotopy.equiv
import fun_groupoid_preserves_homotopic_3
import groupoid_properties
import category_theory.thin

noncomputable theory

section
class contractible (X : Type*) [topological_space X] : Prop :=
(hequiv_unit : nonempty (continuous_map.homotopy_equiv X punit))

variables {X Y Z : Type*} [topological_space X] [contractible X]
  [topological_space Y] [topological_space Z]

instance nonempty_of_contractible : nonempty X :=
begin
  refine nonempty.map (λ hequiv : continuous_map.homotopy_equiv X punit, _) contractible.hequiv_unit,
  exact hequiv.inv_fun punit.star,
end

def nullhomotopic (f : C(Y, Z)) : Prop := ∃ z : Z, continuous_map.homotopic f (continuous_map.const z)

lemma contractible_iff_id_nullhomotopic [nonempty Y] :
  contractible Y ↔ nullhomotopic (continuous_map.id : C(Y, Y))  :=
begin
  split,
  { rintro ⟨⟨hequiv_unit⟩⟩,
    use hequiv_unit.inv_fun punit.star,
    have : continuous_map.const (hequiv_unit.inv_fun punit.star) = hequiv_unit.inv_fun.comp hequiv_unit.to_fun :=
    by { ext, simp, congr, },
    simp only [continuous_map.id_coe, id.def, this],
    exact hequiv_unit.left_inv.symm, },
  { rintro ⟨y, id_to_y⟩,
    refine {hequiv_unit := ⟨_⟩},
    refine_struct 
    { to_fun := continuous_map.const punit.star, 
      inv_fun := continuous_map.const y, },
    { convert id_to_y.symm, },
    { convert continuous_map.homotopic.refl (continuous_map.id : C(punit, punit)), ext, } }
end

instance path_connected_space_of_contractible : path_connected_space X :=
begin
  have id_null : nullhomotopic (continuous_map.id : C(X, X)) := contractible_iff_id_nullhomotopic.mp infer_instance,
  cases id_null with b id_to_b,
  refine { nonempty := infer_instance, joined := _, },
  intros x y,
  transitivity b,
  { refine nonempty.map (λ H, _) id_to_b,
    exact H.to_path x, },
  { refine nonempty.map (λ H, _) id_to_b.symm, 
    exact H.to_path y, },
end

lemma nullhomotopic_comp_left {Z' : Type*} [topological_space Z'] (f : C(Y, Z)) (nhf : nullhomotopic f) (g : C(Z, Z')) :
  nullhomotopic (g.comp f) :=
begin
  cases nhf with b f_to_const_b,
  use g b,
  exact continuous_map.homotopic.hcomp f_to_const_b (continuous_map.homotopic.refl g),
end
end

namespace fundamental_groupoid
universe u

variables {X : Top.{u}}

section
instance [nonempty X] : nonempty (fundamental_groupoid X) := by assumption
instance [subsingleton X] : subsingleton (fundamental_groupoid X) := by assumption

section
local attribute [instance] path.homotopic.setoid
instance [subsingleton X] {x₀ x₁ : fundamental_groupoid X} : subsingleton (x₀ ⟶ x₁) :=
begin
  rw subsingleton_iff,
  intros f g,
  apply quotient.induction_on₂ f g,
  intros a b,
  congr, ext, simp only [eq_iff_true_of_subsingleton],
end

end

end

section nonempty
local attribute [instance] path.homotopic.setoid
lemma nonempty_path_of_hompath {X : Type*} [topological_space X] {x₀ x₁ : X} (p : path.homotopic.quotient x₀ x₁) : 
  joined x₀ x₁ := quotient.induction_on p nonempty.intro

lemma nonempty_hompath_of_path {X : Type*} [topological_space X] {x₀ x₁ : X} (p : joined x₀ x₁) :
  nonempty (path.homotopic.quotient x₀ x₁) := nonempty.map quotient.mk p
end nonempty


theorem fgrpd_connected_iff_path_connected :
  category_theory.is_connected (fundamental_groupoid X) ↔ path_connected_space X :=
begin
  split,
  { introI grpd_conn,
    refine { nonempty := grpd_conn.is_nonempty, joined := _ },
    intros x y,
    rw category_theory.groupoid.groupoid_connected_iff_hom at grpd_conn,
    apply nonempty_path_of_hompath,
    exact (grpd_conn x y).some, },
  { introI x_conn,
    haveI : nonempty (fundamental_groupoid X) := nonempty.map id x_conn.nonempty,
    rw category_theory.groupoid.groupoid_connected_iff_hom,
    intros a b,
    apply nonempty_hompath_of_path (path_connected_space.joined (to_top a : X) b), },
end

section
class simply_connected (X  : Top.{u}) : Prop := 
(equiv_punit : nonempty ((fundamental_groupoid X) ≌ category_theory.discrete punit))

variables [simply_connected X]

theorem thin_of_simply_connected (x y : fundamental_groupoid X) : subsingleton (x ⟶ y) :=
begin
  apply subsingleton.intro,
  intros a b,
  obtain ⟨equiv_punit : ((fundamental_groupoid X) ≌ category_theory.discrete punit)⟩ := simply_connected.equiv_punit,
  rw ← category_theory.equivalence.functor_map_inj_iff equiv_punit a b,
  ext, { apply_instance, },
end

section
local attribute [instance] path.homotopic.setoid

theorem all_paths_homotopic_of_simply_connect (x y : X) (p₁ p₂ : path x y) : path.homotopic p₁ p₂ :=
quotient.eq.mp (subsingleton_iff.mp (thin_of_simply_connected x y) ⟦p₁⟧ ⟦p₂⟧)

end

instance nonempty_of_simply_connected : nonempty X :=
begin
  refine nonempty.map (λ equiv_punit, _) (@simply_connected.equiv_punit X _),
  exact equiv_punit.inverse.obj punit.star,
end

instance : path_connected_space X :=
begin
  rw ← fgrpd_connected_iff_path_connected,
  rw category_theory.groupoid.groupoid_connected_iff_hom,
  intros a b,
  refine nonempty.map (λ equiv_punit, _) (@simply_connected.equiv_punit X _),
  have ax := (equiv_punit.unit_iso.app a).hom,
  have bx := (equiv_punit.unit_iso.app b).inv, 
  simp [punit_eq_star (equiv_punit.functor.obj a)] at ax,
  simp [punit_eq_star (equiv_punit.functor.obj b)] at bx,
  exact ax ≫ bx,
end



variables {Y : Top.{u}} [contractible.{u u} Y]

set_option pp.universes true
section punit
private def π := fundamental_groupoid.fundamental_groupoid_functor

def fgrpd_to_unit : (fundamental_groupoid (Top.of punit : Top.{u})) ⥤ (category_theory.discrete punit : Type u) :=
{ obj := λ a, a,
  map := λ a a' f, category_theory.eq_to_hom (punit_eq a a'),
  map_id' := λ a, by simp,
  map_comp' := λ a a' a'', by simp, }

def unit_to_fgrpd : (category_theory.discrete punit) ⥤ (fundamental_groupoid (Top.of punit)) :=
{ obj := λ a, a,
  map := λ a a' f, category_theory.eq_to_hom (punit_eq a a'),
  map_id' := λ a, by simp,
  map_comp' := λ a a' a'', by simp, }

lemma top_punit_subsingleton : subsingleton (Top.of punit) :=
begin
  rw subsingleton_iff, intros,
  exact punit_eq x y,
end

local attribute [instance] top_punit_subsingleton

def punit_fgrpd : fundamental_groupoid (Top.of punit) ≌ category_theory.discrete punit.{u+1} :=
begin
  apply category_theory.equivalence.mk fgrpd_to_unit unit_to_fgrpd;
  refine category_theory.eq_to_iso _;
  apply category_theory.functor.ext;
  { intros, simp, },
end


instance simply_connected_punit : simply_connected (Top.of punit.{u+1}) :=
{ equiv_punit := nonempty.intro punit_fgrpd, }

end punit

instance simply_connected_of_contractible : simply_connected.{u} Y :=
begin
  refine { equiv_punit := nonempty.map (λ hequiv_unit, _) (@contractible.hequiv_unit Y _ _), },
  suffices : fundamental_groupoid Y ≌ fundamental_groupoid (Top.of punit.{u+1}),
  { exact this.trans punit_fgrpd, },
  refine equivalent_fundamental_groupoids Y (Top.of punit : Top.{u}) _,
  exact hequiv_unit,
end

end

end fundamental_groupoid
