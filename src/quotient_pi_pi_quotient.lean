import data.quot
import data.equiv.basic
import tactic.interactive
import tactic.ext

noncomputable theory
namespace pi_quotient

section
parameters {I : Type*} {α : I → Type*} [∀ i, setoid (α i)]


abbreviation quotient_pi := @quotient (Π i, α i) infer_instance
abbreviation pi_quotient := (Π i, @quotient (α i) infer_instance)

def f (x : Π i, α i) : pi_quotient := λ i, ⟦x i⟧
lemma f_preserves_rel : ∀ x y : Π i, α i, x ≈ y → f x = f y :=
begin
  intros x y hxy,
  ext i,
  change ⟦x i⟧ = ⟦y i⟧,
  simp only [quotient.eq],
  apply hxy,
end

def f_quot : quotient_pi → pi_quotient := quotient.lift f f_preserves_rel
lemma f_equiv : function.bijective f_quot :=
begin
  split,
  { intros x y hxy,
    cases quotient.exists_rep x with x' hx',
    cases quotient.exists_rep y with y' hy',
    subst hx', subst hy',
    change f x' = f y' at hxy,
    rw quotient.eq, intro i, rw ← quotient.eq,
    have : f x' i = f y' i := by rw hxy,
    exact this, },
  { intro x,
    have : ∀ i : I, ∃ x' : α i, ⟦x'⟧ = x i := by { intro i, exact quotient.exists_rep _, },
    rw classical.skolem at this,
    cases this with y hy,
    use ⟦y⟧,
    ext i,
    change ⟦y i⟧ = x i,
    exact hy i, }
end

def f_equiv' : quotient_pi ≃ pi_quotient
   := equiv.of_bijective f_quot f_equiv


lemma f_equiv_rec_forward :
  ∀ x : Π i, α i, f_equiv' ⟦x⟧ = λ i, ⟦x i⟧
  := by { intro, refl, }

lemma f_equiv_rec_backward :
  ∀ x : Π i, α i, ⟦x⟧ = f_equiv'.inv_fun (λ i, ⟦x i⟧)
  :=
begin
  intro x,
  have forward := f_equiv_rec_forward x,
  have : f_equiv'.inv_fun (f_equiv' ⟦x⟧) = f_equiv'.inv_fun (λ i : I, ⟦x i⟧)
    := by rw forward,
  simp at this,
  assumption,
end


end --section
end pi_quotient