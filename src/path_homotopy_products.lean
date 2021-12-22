import topology.homotopy.basic
import topology.homotopy.path
import topology.category.Top.basic
import topology.path_connected
import quotient_pi_pi_quotient
import homotopy_products
import data.quot
import hcomp

noncomputable theory

def to_bundled {α β : Type*} [topological_space α] [topological_space β]
               {f : α → β} (cf : continuous f) : C(α, β) := {to_fun := f}


namespace path.homotopic
section outer
local attribute [instance] path.homotopic.setoid
parameters {I : Type*} {X : I → Top}

section product_descends_to_homotopy
parameters {as bs : Π i, X i}

def path_prod (paths : Π i, path (as i) (bs i)) : path as bs := 
{
  to_continuous_map := continuous_map.pi (λ i, (paths i).to_continuous_map),
  source' := by simp,
  target' := by simp,
}

def path_homotopy 
  (paths₀ paths₁ : Π i, path (as i) (bs i))
  (homotopies : ∀ i, path.homotopy (paths₀ i) (paths₁ i))
  : path.homotopy (path_prod paths₀) (path_prod paths₁) :=
  continuous_map.homotopy.product_homotopy
    (λ i, (paths₀ i).to_continuous_map)
    (λ i, (paths₁ i).to_continuous_map)
    {0, 1}
    homotopies


section

-- Relies on the axiom of choice in a crucial way:
-- We are only given that there is some homotopy in each space
-- between the paths but we pick a homotopy for each one 
-- to construct the product homotopy
lemma path_prod_preserves_homotopic
  : ((≈) ⇒ (≈)) path_prod path_prod
  :=
begin
  intros x y hxy,
  change (∀ i, nonempty ((x i).homotopy (y i))) at hxy,
  rw ← classical.nonempty_pi at hxy,
  exact nonempty.map (path_homotopy x y) hxy,
end

def path_prod.quotient (paths : Π i, path.homotopic.quotient (as i) (bs i))
  : path.homotopic.quotient as bs := 
  (quotient.map path_prod path_prod_preserves_homotopic)
    (pi_quotient.f_equiv'.inv_fun paths)

lemma path_prod.quotient_rec : 
  ∀ x : Π i, path (as i) (bs i),
  path_prod.quotient (λ i, ⟦x i⟧) = ⟦path_prod x⟧ :=
begin
  intro x,
  change (quotient.map path_prod _)
          (pi_quotient.f_equiv'.inv_fun (λ i, ⟦x i⟧)) = _,
  rw ← pi_quotient.f_equiv_rec_backward x,
  refl,
end

end
end product_descends_to_homotopy


section prod_comm_comp
-- Products commute with path composition
-- i.e. (Πa, P₁ a) ⬝ (Πa, P₂ a) = Πa, (P₁ a ⬝ P₂ a)
parameters {as bs cs : Π i, X i}

local notation p₁ ` ⬝ ` p₂ := path.trans p₁ p₂

lemma path_trans_commutes_with_product
            (paths₀ : Π i, path (as i) (bs i))
            (paths₁ : Π i, path (bs i) (cs i))
          : ((path_prod paths₀) ⬝ (path_prod paths₁)) =
            (path_prod (λ i, (paths₀ i) ⬝ (paths₁ i)))
  := 
begin
  ext t i,
  change ((path_prod paths₀) ⬝ (path_prod paths₁)) t i = (paths₀ i ⬝ paths₁ i) t,
  unfold path.trans,
  simp only [path.coe_mk, function.comp_app],
  split_ifs;
    refl,
end



local notation p₁ ` ⬝ ` p₂ := path.homotopic.hcomp.quotient p₁ p₂

lemma hompath_trans_commutes_with_product
      (paths₀ : Π i, path.homotopic.quotient (as i) (bs i))
      (paths₁ : Π i, path.homotopic.quotient (bs i) (cs i))
    : ((path_prod.quotient paths₀) ⬝ (path_prod.quotient paths₁))
      = (path_prod.quotient (λ i, (paths₀ i) ⬝ (paths₁ i))) :=
begin
  have path₀_rep := (λ i : I, quotient.exists_rep (paths₀ i)),
  have path₁_rep := λ i : I, quotient.exists_rep (paths₁ i),
  rw classical.skolem at path₀_rep,
  rw classical.skolem at path₁_rep,
  cases path₀_rep with a ha,
  cases path₁_rep with b hb,
  have ha' : paths₀ = λ i, ⟦a i⟧ := by { ext i, exact (ha i).symm, },
  have hb' : paths₁ = λ i, ⟦b i⟧ := by { ext i, exact (hb i).symm, },
  
  rw [ha', hb'],
  simp only [path_prod.quotient_rec],
  rw [← path.homotopic.hcomp.quotient_lift,
      path_trans_commutes_with_product,
      ← path_prod.quotient_rec],
  refl,
end
end prod_comm_comp


lemma id_product_is_id (xs : Π i, X i) 
  : path_prod (λ i : I, path.refl (xs i)) = path.refl xs
  := rfl

lemma id_product_is_id.quotient (xs : Π i, X i)
  : path_prod.quotient (λ i, ⟦path.refl (xs i)⟧) = ⟦path.refl xs⟧
  := by rw [path_prod.quotient_rec, id_product_is_id]


section projection_descends_to_homotopy
parameters {as bs : Π i, X i}

def path_proj (i : I) (p : path as bs) : path (as i) (bs i) :=
{ to_fun := p.map (continuous_apply i),
  source' := by simp,
  target' := by simp, }

def proj_homotopy (i : I) (path₀ path₁ : path as bs)
           (homotopies : path.homotopy path₀ path₁)
        : path.homotopy (path_proj i path₀) (path_proj i path₁)
        := homotopies.map (to_bundled (continuous_apply i))


section

lemma path_proj_preserves_homotopic (i : I) : ((≈) ⇒ (≈)) (path_proj i) (path_proj i)
  := λ x y, nonempty.map (proj_homotopy i x y)

def path_proj.quotient (i : I)
  : path.homotopic.quotient as bs → path.homotopic.quotient (as i) (bs i)
  := quotient.map (path_proj i) (path_proj_preserves_homotopic i)

lemma path_proj.quotient_rec (i : I) (p : path as bs)
  : (path_proj.quotient i ⟦p⟧) = ⟦path_proj i p⟧ := rfl 
end

end projection_descends_to_homotopy

section proj_comm_comp
local notation p₁ ` ⬝ ` p₂ := path.trans p₁ p₂
parameters {as bs cs : Π i, X i}
lemma proj_commutes_with_comp (i : I)
      (p₀ : path as bs) (p₁ : path bs cs) :
      path_proj i (p₀ ⬝ p₁) = ((path_proj i p₀) ⬝ (path_proj i p₁))
      :=
begin
  ext t,
  change (p₀ ⬝ p₁) t i = _,
  unfold path.trans,
  simp only [path.coe_mk, function.comp_app],
  split_ifs;
    refl,
end


local notation p₁ ` ⬝ ` p₂ := path.homotopic.hcomp.quotient p₁ p₂

lemma homproj_commutes_with_comp (i : I) {p₀ : path.homotopic.quotient as bs} {p₁ : path.homotopic.quotient bs cs}
      : path_proj.quotient i (p₀ ⬝ p₁) = ((path_proj.quotient i p₀) ⬝ (path_proj.quotient i p₁))
      :=
begin
  intros,
  apply quotient.induction_on₂ p₀ p₁,
  intros p₀_lift p₁_lift,
  rw [
    ← path.homotopic.hcomp.quotient_lift,
    path_proj.quotient_rec, path_proj.quotient_rec, path_proj.quotient_rec,
    ← path.homotopic.hcomp.quotient_lift,
    proj_commutes_with_comp
  ],
end

end proj_comm_comp

section proj_id

lemma proj_id_is_id (i : I) (xs : Π i, X i)
        : path_proj i (path.refl xs) = path.refl (xs i) := rfl

lemma proj_id_is_id.quotient (i : I) (xs : Π i, X i)
        : path_proj.quotient i ⟦path.refl xs⟧ = ⟦path.refl (xs i)⟧ :=
  by { rw path_proj.quotient_rec i, rw proj_id_is_id, }

end proj_id

section inverses
parameters {as bs : Π i, X i}

@[simp]
lemma proj_prod (i : I) (paths : Π i, path (as i) (bs i))
  : path_proj i (path_prod paths) = paths i := by { ext, refl, }

@[simp]
lemma proj_prod.quotient (i : I)
  (paths : Π i, path.homotopic.quotient (as i) (bs i))
  : path_proj.quotient i (path_prod.quotient paths) = paths i
  :=
begin
  have rep := λ i : I, quotient.exists_rep (paths i),
  rw classical.skolem at rep,
  cases rep with a ha,
  have ha' : paths = λ i, ⟦a i⟧ := by { ext i, exact (ha i).symm, },
  rw ha',
  rw path_prod.quotient_rec, rw path_proj.quotient_rec,
  simp,
end

@[simp]
lemma prod_proj (p : path as bs)
  : path_prod (λ i, path_proj i p) = p := by { ext, refl, }

@[simp]
lemma prod_proj.quotient (p : path.homotopic.quotient as bs)
  : path_prod.quotient (λ i, path_proj.quotient i p) = p :=
begin
  apply @quotient.induction_on _ _
    (λ (a : path.homotopic.quotient as bs), path_prod.quotient (λ i, path_proj.quotient i a) = a),
  intro a,
  simp_rw path_proj.quotient_rec,
  rw path_prod.quotient_rec,
  simp,
end
end inverses
end outer
end path.homotopic

