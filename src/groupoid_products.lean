import category_theory.groupoid
import category_theory.products.basic
import category_theory.functor
import category_theory.pi.basic



universe u

/-
 - Here we show that the product of groupoids has a groupoid
 - structure, which is an extension of the product category structure
-/
section
parameters {I : Type u} {J : I → Type u} 
        [∀i : I, category_theory.groupoid.{u} (J i)]


instance groupoid_pi : category_theory.groupoid.{u} (Πi : I, J i) := 
{
  inv := λ (x y : Πi : I, J i) (f : Π i : I, x i ⟶ y i), 
          (λ i : I, category_theory.groupoid.inv (f i)),
}

end

section
parameters {α β : Type u} [category_theory.groupoid.{u} α] [category_theory.groupoid.{u} β]

instance groupoid_prod : category_theory.groupoid.{u} (α × β) :=
{
  inv := λ (x y : α × β) (f : x ⟶ y), 
        (category_theory.groupoid.inv f.1, category_theory.groupoid.inv f.2)
}

end