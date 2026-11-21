/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # CF5 for individually existing colimits of discrete functors -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
variable {ι : Type w} {M : Type u} [Category.{v} M]

/-- A colimit of a discrete functor is a coproduct with its canonical legs. -/
noncomputable def discreteColimitCofan (F : Discrete ι ⥤ M) [HasColimit F] :
    Cofan (fun i ↦ F.obj ⟨i⟩) := Cofan.mk (colimit F) (fun i ↦ colimit.ι F ⟨i⟩)

/-- The canonical cofan is a coproduct even when the functor is not syntactically
`Discrete.functor` of its object family. -/
noncomputable def isColimitDiscreteColimitCofan (F : Discrete ι ⥤ M) [HasColimit F] :
    IsColimit (discreteColimitCofan F) :=
  Cofan.IsColimit.mk _
    (fun c ↦ colimit.desc F
      { pt := c.pt
        ι := (Discrete.natIsoFunctor (F := F)).hom ≫ c.ι })
    (fun c i ↦ by simp [discreteColimitCofan, Cofan.inj])
    (fun c f hf ↦ by
      apply colimit.hom_ext (F := F)
      rintro ⟨i⟩
      simpa [discreteColimitCofan, Cofan.inj] using hf i)

variable [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCCofibrationCategory.{w} M]

/-- CF5 supplies colimits of all discrete functors on cofibrant objects. -/
theorem hasColimit_discrete_of_cofibrant (F : Discrete ι ⥤ M)
    (hF : ∀ i, IsCofibrant (F.obj i)) : HasColimit F := by
  have : HasCoproduct (fun i : ι ↦ F.obj ⟨i⟩) :=
    ABCCofibrationCategory.hasCoproductOfCofibrant _ (fun i ↦ hF ⟨i⟩)
  have : HasColimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
    inferInstanceAs (HasCoproduct (fun i : ι ↦ F.obj ⟨i⟩))
  exact hasColimit_of_iso Discrete.natIsoFunctor

/-- Cofibrancy does not depend on the syntactic presentation of a discrete functor. -/
theorem isCofibrant_colimit_discrete (F : Discrete ι ⥤ M) [HasColimit F]
    (hF : ∀ i, IsCofibrant (F.obj i)) : IsCofibrant (colimit F) :=
  ABCCofibrationCategory.isCofibrant_of_isColimit _ (fun i ↦ hF ⟨i⟩)
    (isColimitDiscreteColimitCofan F)

/-- CF5 preserves cofibrations for maps of arbitrary discrete functors. -/
theorem cofibration_colimMap_discrete {F G : Discrete ι ⥤ M}
    [HasColimit F] [HasColimit G] (f : F ⟶ G)
    (hF : ∀ i, IsCofibrant (F.obj i)) (hf : ∀ i, Cofibration (f.app i)) :
    Cofibration (colimMap f) :=
  ABCCofibrationCategory.cofibration_of_isColimit (fun i : ι ↦ f.app ⟨i⟩)
    (fun i ↦ hF ⟨i⟩) (fun i ↦ hf ⟨i⟩) (isColimitDiscreteColimitCofan F)
    (isColimitDiscreteColimitCofan G) (colimMap f) (fun i ↦ ι_colimMap f ⟨i⟩)

end ABCCofibrations
