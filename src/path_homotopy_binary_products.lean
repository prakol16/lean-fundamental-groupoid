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
variables {α β : Top} {a₁ a₂ a₃ : α} {b₁ b₂ b₃ : β} 

section prod
variables (p₁ p₁' : path a₁ a₂) (p₂ p₂' : path b₁ b₂)
          (q₁ : path.homotopic.quotient a₁ a₂) (q₂ : path.homotopic.quotient b₁ b₂)
          (r₁ : path a₂ a₃) (r₂ : path b₂ b₃)
          (s₁ : path.homotopic.quotient a₂ a₃) (s₂ : path.homotopic.quotient b₂ b₃)


def prod (p₁ : path a₁ a₂) (p₂ : path b₁ b₂) : path (a₁, b₁) (a₂, b₂) :=
{ to_continuous_map := continuous_map.prod_mk p₁.to_continuous_map p₂.to_continuous_map,
  source' := by simp,
  target' := by simp, }

def prod_homotopy (h₁ : path.homotopy p₁ p₁') 
                  (h₂ : path.homotopy p₂ p₂') :
                  path.homotopy (prod p₁ p₂) (prod p₁' p₂') :=
  continuous_map.homotopy.prod h₁ h₂

lemma prod_preserves_homotopic : ((≈) ⇒ (≈) ⇒ (≈)) (@prod _ _ a₁ a₂ b₁ b₂) prod :=
  λ p₁ p₁' h₁ p₂ p₂' h₂, nonempty.map2 (prod_homotopy p₁ p₁' p₂ p₂') h₁ h₂

def prod.quotient (q₁ q₂) :
                  path.homotopic.quotient (a₁, b₁) (a₂, b₂) := 
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

end prod

section proj
variables (p p' : path (a₁, b₁) (a₂, b₂))
          (q : path.homotopic.quotient (a₁, b₁) (a₂, b₂))
          (r : path (a₂, b₂) (a₃, b₃))
          (s : path.homotopic.quotient (a₂, b₂) (a₃, b₃))

def proj.left : path a₁ a₂ := 
{  to_fun := p.map continuous_fst,
  source' := by simp,
  target' := by simp, }

def proj.right : path b₁ b₂ := 
{  to_fun := p.map continuous_snd,
  source' := by simp,
  target' := by simp, }

def proj_homotopy.left (h : path.homotopy p p') : 
  path.homotopy (proj.left p) (proj.left p') :=
  h.map ⟨_, continuous_fst⟩

def proj_homotopy.right (h : path.homotopy p p') : 
  path.homotopy (proj.right p) (proj.right p') :=
  h.map ⟨_, continuous_snd⟩

lemma proj_left_preserves_homotopic : ((≈) ⇒ (≈)) (@proj.left _ _ a₁ a₂ b₁ b₂) proj.left :=
  λ p p' hp, nonempty.map (proj_homotopy.left p p') hp

lemma proj_right_preserves_homotopic : ((≈) ⇒ (≈)) (@proj.right _ _ a₁ a₂ b₁ b₂) proj.right :=
  λ p p' hp, nonempty.map (proj_homotopy.right p p') hp

def proj.left.quotient : path.homotopic.quotient a₁ a₂ :=
  (quotient.map proj.left proj_left_preserves_homotopic) q

def proj.right.quotient : path.homotopic.quotient b₁ b₂ :=
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
variables (p₁ : path a₁ a₂) (p₂ : path b₁ b₂)
          (q₁ : path.homotopic.quotient a₁ a₂) (q₂ : path.homotopic.quotient b₁ b₂)

@[simp]
lemma proj_left_prod : proj.left (prod p₁ p₂) = p₁ := by { ext, refl, }
@[simp]
lemma proj_right_prod : proj.right (prod p₁ p₂) = p₂ := by { ext, refl, }

@[simp]
lemma proj_left_prod.quotient : proj.left.quotient (prod.quotient q₁ q₂) = q₁ :=
begin
  apply quotient.induction_on₂ q₁ q₂,
  intros p₁ p₂,
  simp only [prod.quotient_rec, proj_left_quotient_rec, proj_left_prod],
end

@[simp]
lemma proj_right_prod.quotient : proj.right.quotient (prod.quotient q₁ q₂) = q₂ :=
begin
  apply quotient.induction_on₂ q₁ q₂,
  intros p₁ p₂,
  simp only [prod.quotient_rec, proj_right_quotient_rec, proj_right_prod],
end

end inverses
end path.homotopic
