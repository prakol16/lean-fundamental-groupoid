import topology.homotopy.path

noncomputable theory

namespace path.homotopic
section
parameters {A : Type*} [topological_space A] {x y z : A}
local attribute [instance] path.homotopic.setoid


def hcomp.quotient : path.homotopic.quotient x y
                   → path.homotopic.quotient y z
                   → path.homotopic.quotient x z
  := quotient.map₂ path.trans
    (λ (p₀ : path x y) p₁ hp q₀ q₁ hq, path.homotopic.hcomp hp hq)


lemma hcomp.quotient_lift (a : path x y)
                          (b : path y z)
                          : ⟦a.trans b⟧ = hcomp.quotient ⟦a⟧ ⟦b⟧
                          := rfl
end
end path.homotopic