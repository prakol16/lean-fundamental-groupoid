import data.quot
import data.equiv.basic
import tactic.interactive
import tactic.ext

noncomputable theory
namespace quotient
variables {I : Type*} {α : I → Sort*} [s : ∀ i, setoid (α i)]

attribute [elab_as_eliminator]
lemma induction_pi {φ : (Π i : I, quotient (s i)) → Prop} (q : Π i : I, quotient (s i))
      (hi : ∀ a : Π i : I, α i, φ (λ i, ⟦a i⟧)) : φ q :=
begin
  have q_lift := λi : I, quotient.exists_rep (q i),
  rw classical.skolem at q_lift,
  cases q_lift with f hf,
  have q_lift_eq_f : (λ i : I, ⟦f i⟧) = q := by { ext, apply hf, },
  rw ← q_lift_eq_f,
  exact hi f,
end
end quotient

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
  { intros x y,
    apply quotient.induction_on₂ x y,
    intros x' y' hxy,
    rw quotient.eq, intro i, rw ← quotient.eq,
    exact function.funext_iff.mp hxy i, },
  { intro x,
    apply quotient.induction_pi x,
    intro x',
    use ⟦x'⟧,
    refl, }
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