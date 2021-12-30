import homotopy_binary_products
import topology.homotopy.basic
import topology.homotopy.path
import topology.category.Top.basic
import topology.path_connected
import quotient_pi_pi_quotient
import homotopy_products
import data.quot
import hcomp

noncomputable theory


namespace path.homotopic
local attribute [instance] path.homotopic.setoid
variables {α β : Top} --{a₁ a₂ a₃ : α} {b₁ b₂ b₃ : β}
          {c₁ c₂ c₃ : α × β}

section prod
variables (p₁ p₁' : path c₁.1 c₂.1) (p₂ p₂' : path c₁.2 c₂.2)
          (q₁ : path.homotopic.quotient c₁.1 c₂.1) (q₂ : path.homotopic.quotient c₁.2 c₂.2)
          (r₁ : path c₂.1 c₃.1) (r₂ : path c₂.2 c₃.2)
          (s₁ : path.homotopic.quotient c₂.1 c₃.1) (s₂ : path.homotopic.quotient c₂.2 c₃.2)


def prod (p₁ : path c₁.1 c₂.1) (p₂ : path c₁.2 c₂.2) : path c₁ c₂ :=
{ to_continuous_map := continuous_map.prod_mk p₁.to_continuous_map p₂.to_continuous_map,
  source' := by simp,
  target' := by simp, }

variables {p₁ p₁' p₂ p₂'}
def prod_homotopy (h₁ : path.homotopy p₁ p₁') 
                  (h₂ : path.homotopy p₂ p₂') :
                  path.homotopy (prod p₁ p₂) (prod p₁' p₂') :=
  continuous_map.homotopy.prod h₁ h₂

variables (p₁ p₁' p₂ p₂')
lemma prod_preserves_homotopic : ((≈) ⇒ (≈) ⇒ (≈)) (@prod _ _ c₁ c₂) prod :=
  λ p₁ p₁' h₁ p₂ p₂' h₂, nonempty.map2 prod_homotopy h₁ h₂

def prod.quotient (q₁ q₂) :
                  path.homotopic.quotient c₁ c₂ := 
                  (quotient.map₂ prod prod_preserves_homotopic) q₁ q₂

lemma prod.quotient_rec : prod.quotient ⟦p₁⟧ ⟦p₂⟧ = ⟦prod p₁ p₂⟧ := rfl

local notation a ` ⬝ ` b := path.trans a b
lemma path_trans_comm_prod : prod (p₁ ⬝ r₁) (p₂ ⬝ r₂) = ((prod p₁ p₂) ⬝ (prod r₁ r₂)) :=
begin
  ext t,
  change (p₁ ⬝ r₁) t = _,
  swap, change (p₂ ⬝ r₂) t = _,
  repeat {
    unfold path.trans,
    simp only [path.coe_mk, function.comp_app],
    split_ifs;
      refl,
  }
end


local notation p₁ ` ⬝ ` p₂ := path.homotopic.hcomp.quotient p₁ p₂
lemma hcomp_comm_prod : prod.quotient (q₁ ⬝ s₁) (q₂ ⬝ s₂) = ((prod.quotient q₁ q₂) ⬝ (prod.quotient s₁ s₂)) :=
begin
  apply quotient.induction_on₂ s₁ s₂,
  apply quotient.induction_on₂ q₁ q₂,
  intros p₁ p₂ r₁ r₂,
  simp only [prod.quotient_rec, ← hcomp.quotient_lift, path_trans_comm_prod],
end

lemma id_prod : prod (path.refl c₁.1) (path.refl c₁.2) = path.refl c₁ := by { ext; refl, }
lemma id_prod.quotient (a₁ : α) (b₁ : β) :
  prod.quotient ⟦path.refl c₁.1⟧ ⟦path.refl c₁.2⟧ = ⟦path.refl c₁⟧ := by { rw [prod.quotient_rec, id_prod], }

end prod

section proj
variables {c₁ c₂ c₃}
          (p p' : path c₁ c₂)
          (q : path.homotopic.quotient c₁ c₂)
          (r : path c₂ c₃)
          (s : path.homotopic.quotient c₂ c₃)

def proj.left : path c₁.1 c₂.1 := 
{  to_fun := p.map continuous_fst,
  source' := by simp,
  target' := by simp, }

def proj.right : path c₁.2 c₂.2 := 
{  to_fun := p.map continuous_snd,
  source' := by simp,
  target' := by simp, }

def proj_homotopy.left (h : path.homotopy p p') : 
  path.homotopy (proj.left p) (proj.left p') :=
  h.map ⟨_, continuous_fst⟩

def proj_homotopy.right (h : path.homotopy p p') : 
  path.homotopy (proj.right p) (proj.right p') :=
  h.map ⟨_, continuous_snd⟩

lemma proj_left_preserves_homotopic : ((≈) ⇒ (≈)) (@proj.left _ _ c₁ c₂) proj.left :=
  λ p p' hp, nonempty.map (proj_homotopy.left p p') hp

lemma proj_right_preserves_homotopic : ((≈) ⇒ (≈)) (@proj.right _ _ c₁ c₂) proj.right :=
  λ p p' hp, nonempty.map (proj_homotopy.right p p') hp

def proj.left.quotient : path.homotopic.quotient c₁.1 c₂.1 :=
  (quotient.map proj.left proj_left_preserves_homotopic) q

def proj.right.quotient : path.homotopic.quotient c₁.2 c₂.2 :=
  (quotient.map proj.right proj_right_preserves_homotopic) q

lemma proj_left_quotient_rec : proj.left.quotient ⟦p⟧ = ⟦proj.left p⟧ := rfl
lemma proj_right_quotient_rec : proj.right.quotient ⟦p⟧ = ⟦proj.right p⟧ := rfl

local notation a ` ⬝ ` b := path.trans a b
lemma path_trans_comm_proj_left : proj.left (p ⬝ r) = ((proj.left p) ⬝ (proj.left r)) :=
begin
  ext t,
  change ((p ⬝ r) t).fst = _,
  unfold path.trans,
  simp only [path.coe_mk, function.comp_app],
  split_ifs; refl,
end

lemma path_trans_comm_proj_right : proj.right (p ⬝ r) = ((proj.right p) ⬝ (proj.right r)) :=
begin
  ext t,
  change ((p ⬝ r) t).snd = _,
  unfold path.trans,
  simp only [path.coe_mk, function.comp_app],
  split_ifs; refl,
end

local notation p₁ ` ⬝ ` p₂ := path.homotopic.hcomp.quotient p₁ p₂
lemma hcomp_comm_proj_left : proj.left.quotient (q ⬝ s) = ((proj.left.quotient q) ⬝ (proj.left.quotient s)) :=
begin
  apply quotient.induction_on₂ q s,
  intros p r,
  simp only [proj_left_quotient_rec, ← hcomp.quotient_lift, path_trans_comm_proj_left],
end

lemma hcomp_comm_proj_right : proj.right.quotient (q ⬝ s) = ((proj.right.quotient q) ⬝ (proj.right.quotient s)) :=
begin
  apply quotient.induction_on₂ q s,
  intros p r,
  simp only [proj_right_quotient_rec, ← hcomp.quotient_lift, path_trans_comm_proj_right],
end

end proj

section inverses
variables (p₁ : path c₁.1 c₂.1) (p₂ : path c₁.2 c₂.2)
          (q₁ : path.homotopic.quotient c₁.1 c₂.1) (q₂ : path.homotopic.quotient c₁.2 c₂.2)

@[simp]
lemma proj_left_prod : proj.left (prod p₁ p₂) = p₁ := by { ext, refl, }
@[simp]
lemma proj_right_prod : proj.right (prod p₁ p₂) = p₂ := by { ext, refl, }

@[simp]
lemma proj_left_prod.quotient : proj.left.quotient (prod.quotient q₁ q₂) = q₁ :=
begin
  apply quotient.induction_on₂ q₁ q₂,
  intros p₁ p₂,
  rw [prod.quotient_rec, proj_left_quotient_rec, proj_left_prod],
end

@[simp]
lemma proj_right_prod.quotient : proj.right.quotient (prod.quotient q₁ q₂) = q₂ :=
begin
  apply quotient.induction_on₂ q₁ q₂,
  intros p₁ p₂,
  rw [prod.quotient_rec, proj_right_quotient_rec, proj_right_prod],
end

variables {c d : α × β}
          (p : path c d)
          (q : path.homotopic.quotient c d)

@[simp]
lemma prod_proj' : prod (proj.left p) (proj.right p) = p := by { ext; refl, }


@[simp]
lemma prod_proj.quotient' : prod.quotient (proj.left.quotient q) (proj.right.quotient q) = q :=
begin
    apply quotient.induction_on q,
    intro a,
    rw [proj_left_quotient_rec, proj_right_quotient_rec,
              prod.quotient_rec, prod_proj'],
end

end inverses
end path.homotopic
