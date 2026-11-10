/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Adjoint functors and Kan extensions (§4.2–§4.3)

Propositions 4.2.1, 4.2.2 and 4.3.2 of the paper. They are classical; the
statements are given in the paper's form, and the proofs use mathlib's
adjunction API.

**Terminology.** We use mathlib's terminology, which is the standard one: a
pair `(L, ε : L ∘ γ ⇒ u)` with the terminal universal property is a *right* Kan
extension of `u` along `γ` (`Functor.IsRightKanExtension`), and dually a pair
`(L, η : u ⇒ L ∘ γ)` with the initial universal property is a *left* Kan
extension. Definition 4.3.1 of the paper swaps the two names; this is an error
in the paper, and the statements below are its results with the names
corrected.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Functor Limits

namespace ABCCofibrations

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- **Proposition 4.2.1(1).** Natural maps `φ : 1 ⟶ u₂u₁` and `ψ : u₁u₂ ⟶ 1`
are the unit and counit of an adjunction `u₁ ⊣ u₂` exactly when they satisfy the
triangle identities, and then the adjunction is unique. -/
theorem existsUnique_adjunction_iff {u₁ : A ⥤ B} {u₂ : B ⥤ A} (φ : 𝟭 A ⟶ u₁ ⋙ u₂)
    (ψ : u₂ ⋙ u₁ ⟶ 𝟭 B) :
    (∃! adj : u₁ ⊣ u₂, adj.unit = φ ∧ adj.counit = ψ) ↔
      (∀ X : A, u₁.map (φ.app X) ≫ ψ.app (u₁.obj X) = 𝟙 _) ∧
        ∀ Y : B, φ.app (u₂.obj Y) ≫ u₂.map (ψ.app Y) = 𝟙 _ := by
  constructor
  · rintro ⟨adj, ⟨rfl, rfl⟩, -⟩
    exact ⟨adj.left_triangle_components, adj.right_triangle_components⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨Adjunction.mkOfUnitCounit ⟨φ, ψ, ?_, ?_⟩, ⟨rfl, rfl⟩, ?_⟩
    · ext X
      simpa using h₁ X
    · ext Y
      simpa using h₂ Y
    · rintro adj ⟨hφ, hψ⟩
      ext X
      simp [hφ]

variable {u₁ : A ⥤ B} {u₂ : B ⥤ A} (adj : u₁ ⊣ u₂)

/-- **Proposition 4.2.1(2)(a)**, left adjoint: `u₁` is fully faithful iff the
unit is an isomorphism. -/
theorem full_faithful_left_iff : (u₁.Full ∧ u₁.Faithful) ↔ IsIso adj.unit := by
  constructor
  · rintro ⟨_, _⟩
    infer_instance
  · intro _
    exact ⟨(adj.fullyFaithfulLOfIsIsoUnit).full, (adj.fullyFaithfulLOfIsIsoUnit).faithful⟩

/-- **Proposition 4.2.1(2)(a)**, right adjoint: `u₂` is fully faithful iff the
counit is an isomorphism. -/
theorem full_faithful_right_iff : (u₂.Full ∧ u₂.Faithful) ↔ IsIso adj.counit := by
  constructor
  · rintro ⟨_, _⟩
    infer_instance
  · intro _
    exact ⟨(adj.fullyFaithfulROfIsIsoCounit).full, (adj.fullyFaithfulROfIsIsoCounit).faithful⟩

/-- **Proposition 4.2.1(2)(b).** `u₁` and `u₂` are inverse equivalences iff the
unit and the counit are isomorphisms. -/
theorem inverse_equivalences_iff :
    (∃ e : A ≌ B, e.functor = u₁ ∧ e.inverse = u₂) ↔ IsIso adj.unit ∧ IsIso adj.counit := by
  constructor
  · rintro ⟨e, rfl, rfl⟩
    exact ⟨(full_faithful_left_iff adj).1 ⟨inferInstance, inferInstance⟩,
      (full_faithful_right_iff adj).1 ⟨inferInstance, inferInstance⟩⟩
  · rintro ⟨_, _⟩
    exact ⟨adj.toEquivalence, rfl, rfl⟩

/-- **Proposition 4.2.2**, (1r) ⟺ (2r): a map `u₁A ⟶ B` is an isomorphism if its
adjoint `A ⟶ u₂B` is, exactly when `u₂` is fully faithful. -/
theorem isIso_of_isIso_homEquiv_iff :
    (∀ (X : A) (Y : B) (f : u₁.obj X ⟶ Y), IsIso (adj.homEquiv X Y f) → IsIso f) ↔
      (u₂.Full ∧ u₂.Faithful) := by
  rw [full_faithful_right_iff adj]
  constructor
  · intro h
    have (Y : B) : IsIso (adj.counit.app Y) :=
      h _ _ _ (by rw [Adjunction.homEquiv_unit, adj.right_triangle_components]; infer_instance)
    exact NatIso.isIso_of_isIso_app _
  · intro _ X Y f hf
    rw [← (adj.homEquiv X Y).symm_apply_apply f, Adjunction.homEquiv_counit]
    infer_instance

/-- **Proposition 4.2.2**, (1l) ⟺ (2l): the adjoint of an isomorphism
`u₁A ⟶ B` is an isomorphism exactly when `u₁` is fully faithful. -/
theorem isIso_homEquiv_of_isIso_iff :
    (∀ (X : A) (Y : B) (f : u₁.obj X ⟶ Y), IsIso f → IsIso (adj.homEquiv X Y f)) ↔
      (u₁.Full ∧ u₁.Faithful) := by
  rw [full_faithful_left_iff adj]
  constructor
  · intro h
    have (X : A) : IsIso (adj.unit.app X) := by
      have := h X _ (𝟙 _) inferInstance
      simpa [Adjunction.homEquiv_unit] using this
    exact NatIso.isIso_of_isIso_app _
  · intro _ X Y f _
    rw [Adjunction.homEquiv_unit]
    infer_instance

/-- **Proposition 4.2.2**, (1) ⟺ (2): a map `u₁A ⟶ B` is an isomorphism iff its
adjoint is, exactly when `u₁` and `u₂` are inverse equivalences. -/
theorem isIso_iff_isIso_homEquiv_iff :
    (∀ (X : A) (Y : B) (f : u₁.obj X ⟶ Y), IsIso f ↔ IsIso (adj.homEquiv X Y f)) ↔
      ∃ e : A ≌ B, e.functor = u₁ ∧ e.inverse = u₂ := by
  rw [inverse_equivalences_iff adj, ← full_faithful_left_iff adj,
    ← full_faithful_right_iff adj, ← isIso_of_isIso_homEquiv_iff adj,
    ← isIso_homEquiv_of_isIso_iff adj]
  exact ⟨fun h ↦ ⟨fun X Y f ↦ (h X Y f).1, fun X Y f ↦ (h X Y f).2⟩,
    fun h X Y f ↦ ⟨h.1 X Y f, h.2 X Y f⟩⟩

section Kan

variable {A' : Type u₃} [Category.{v₃} A'] {γ : A ⥤ A'} {γ' : A' ⥤ A}
  {C : Type*} [Category C] (u : A ⥤ C)

/-- **Proposition 4.3.2(1).** If `γ` has a left adjoint `γ'` with counit
`ψ : γ'γ ⟶ 1`, then `(uγ', uψ)` is a right Kan extension of `u` along `γ`. -/
theorem isRightKanExtension_of_isLeftAdjoint (adj : γ' ⊣ γ) :
    (γ' ⋙ u).IsRightKanExtension (whiskerRight adj.counit u : γ ⋙ γ' ⋙ u ⟶ u) := by
  refine ⟨⟨IsTerminal.ofUniqueHom (fun G ↦ CostructuredArrow.homMk
    (whiskerRight adj.unit G.left ≫ whiskerLeft γ' G.hom) ?_) ?_⟩⟩
  · ext X
    have := G.hom.naturality (adj.counit.app X)
    dsimp at this ⊢
    rw [Category.assoc, ← this, ← Category.assoc, ← G.left.map_comp,
      adj.right_triangle_components, G.left.map_id, Category.id_comp]
  · intro G m
    ext Y
    have h₁ := m.left.naturality (adj.unit.app Y)
    have h₂ := congrArg (fun t ↦ NatTrans.app t (γ'.obj Y)) (CostructuredArrow.w m)
    dsimp at h₁ h₂ ⊢
    rw [← h₂, ← Category.assoc, h₁, Category.assoc, ← u.map_comp,
      adj.left_triangle_components, u.map_id, Category.comp_id]

/-- **Proposition 4.3.2(2).** If `γ` has a right adjoint `γ'` with unit
`φ : 1 ⟶ γ'γ`, then `(uγ', uφ)` is a left Kan extension of `u` along `γ`. -/
theorem isLeftKanExtension_of_isRightAdjoint (adj : γ ⊣ γ') :
    (γ' ⋙ u).IsLeftKanExtension (whiskerRight adj.unit u : u ⟶ γ ⋙ γ' ⋙ u) := by
  refine ⟨⟨IsInitial.ofUniqueHom (fun G ↦ StructuredArrow.homMk
    (whiskerLeft γ' G.hom ≫ whiskerRight adj.counit G.right) ?_) ?_⟩⟩
  · ext X
    have := G.hom.naturality (adj.unit.app X)
    dsimp at this ⊢
    rw [← Category.assoc, this, Category.assoc, ← G.right.map_comp,
      adj.left_triangle_components, G.right.map_id, Category.comp_id]
  · intro G m
    ext Y
    have h₁ := m.right.naturality (adj.counit.app Y)
    have h₂ := congrArg (fun t ↦ NatTrans.app t (γ'.obj Y)) (StructuredArrow.w m)
    dsimp at h₁ h₂ ⊢
    rw [← h₂, Category.assoc, ← h₁, ← Category.assoc, ← u.map_comp,
      adj.right_triangle_components, u.map_id, Category.id_comp]

end Kan

section Composition

variable {A' : Type u₃} [Category.{v₃} A'] {A'' : Type*} [Category A'']
  {C : Type*} [Category C] {γ : A ⥤ A'} {γ' : A' ⥤ A''} {u : A ⥤ C}

/-- **Proposition 4.3.3(1)**, the comparison. Let `(F', α)` be a right Kan
extension of `u` along `γ`. Then `(G, β)` is a right Kan extension of `F'` along
`γ'` iff `(G, β ⋆ α)` is a right Kan extension of `u` along `γ'γ`. -/
theorem isRightKanExtension_comp_iff {F' : A' ⥤ C} (α : γ ⋙ F' ⟶ u)
    [F'.IsRightKanExtension α] {G : A'' ⥤ C} (β : γ' ⋙ G ⟶ F') :
    G.IsRightKanExtension β ↔
      G.IsRightKanExtension ((associator γ γ' G).hom ≫ whiskerLeft γ β ≫ α) := by
  constructor
  · intro _
    refine ⟨⟨IsTerminal.ofUniqueHom (fun H ↦ CostructuredArrow.homMk
      (G.liftOfIsRightKanExtension β H.left
        (F'.liftOfIsRightKanExtension α (γ' ⋙ H.left) ((associator _ _ _).inv ≫ H.hom)))
      ?_) ?_⟩⟩
    · ext X
      simp
    · intro H m
      have hm := CostructuredArrow.w m
      refine CostructuredArrow.hom_ext _ _ ?_
      dsimp
      apply G.hom_ext_of_isRightKanExtension β
      rw [liftOfIsRightKanExtension_fac]
      apply F'.hom_ext_of_isRightKanExtension α
      rw [liftOfIsRightKanExtension_fac]
      ext X
      have := congr_app hm X
      dsimp at this ⊢
      simpa using this
  · intro _
    refine ⟨⟨IsTerminal.ofUniqueHom (fun H ↦ CostructuredArrow.homMk
      (G.liftOfIsRightKanExtension ((associator γ γ' G).hom ≫ whiskerLeft γ β ≫ α) H.left
        ((associator _ _ _).hom ≫ whiskerLeft γ H.hom ≫ α)) ?_) ?_⟩⟩
    · apply F'.hom_ext_of_isRightKanExtension α
      ext X
      have := congr_app (G.liftOfIsRightKanExtension_fac
        ((associator γ γ' G).hom ≫ whiskerLeft γ β ≫ α) H.left
        ((associator _ _ _).hom ≫ whiskerLeft γ H.hom ≫ α)) X
      dsimp at this ⊢
      simpa using this
    · intro H m
      have hm := CostructuredArrow.w m
      refine CostructuredArrow.hom_ext _ _ ?_
      dsimp
      apply G.hom_ext_of_isRightKanExtension ((associator γ γ' G).hom ≫ whiskerLeft γ β ≫ α)
      rw [liftOfIsRightKanExtension_fac]
      ext X
      have := congr_app hm (γ.obj X)
      dsimp at this ⊢
      simp [← this]

/-- **Proposition 4.3.3(1).** If `(F', α)` is a right Kan extension of `u` along
`γ`, then a right Kan extension of `F'` along `γ'` exists iff one of `u` along
`γ'γ` does. -/
theorem hasRightKanExtension_comp_iff {F' : A' ⥤ C} (α : γ ⋙ F' ⟶ u)
    [F'.IsRightKanExtension α] :
    HasRightKanExtension γ' F' ↔ HasRightKanExtension (γ ⋙ γ') u := by
  constructor
  · intro _
    have := (isRightKanExtension_comp_iff α (γ'.rightKanExtensionCounit F')).1 inferInstance
    exact HasRightKanExtension.mk _ ((associator γ γ' _).hom ≫
      whiskerLeft γ (γ'.rightKanExtensionCounit F') ≫ α)
  · intro _
    let β := F'.liftOfIsRightKanExtension α (γ' ⋙ (γ ⋙ γ').rightKanExtension u)
      ((associator _ _ _).inv ≫ (γ ⋙ γ').rightKanExtensionCounit u)
    have h : (associator γ γ' _).hom ≫ whiskerLeft γ β ≫ α =
        (γ ⋙ γ').rightKanExtensionCounit u := by
      ext X
      simp [β]
    have := (isRightKanExtension_comp_iff α β).2 (by rw [h]; infer_instance)
    exact HasRightKanExtension.mk _ β

/-- **Proposition 4.3.3(2)**, the comparison. Let `(F', α)` be a left Kan
extension of `u` along `γ`. Then `(G, β)` is a left Kan extension of `F'` along
`γ'` iff `(G, α ⋆ β)` is a left Kan extension of `u` along `γ'γ`. -/
theorem isLeftKanExtension_comp_iff {F' : A' ⥤ C} (α : u ⟶ γ ⋙ F')
    [F'.IsLeftKanExtension α] {G : A'' ⥤ C} (β : F' ⟶ γ' ⋙ G) :
    G.IsLeftKanExtension β ↔
      G.IsLeftKanExtension (α ≫ whiskerLeft γ β ≫ (associator γ γ' G).inv) := by
  constructor
  · intro _
    refine ⟨⟨IsInitial.ofUniqueHom (fun H ↦ StructuredArrow.homMk
      (G.descOfIsLeftKanExtension β H.right
        (F'.descOfIsLeftKanExtension α (γ' ⋙ H.right) (H.hom ≫ (associator _ _ _).hom)))
      ?_) ?_⟩⟩
    · ext X
      simp
    · intro H m
      have hm := StructuredArrow.w m
      refine StructuredArrow.hom_ext _ _ ?_
      dsimp
      apply G.hom_ext_of_isLeftKanExtension β
      rw [descOfIsLeftKanExtension_fac]
      apply F'.hom_ext_of_isLeftKanExtension α
      rw [descOfIsLeftKanExtension_fac]
      ext X
      have := congr_app hm X
      dsimp at this ⊢
      simpa using this
  · intro _
    refine ⟨⟨IsInitial.ofUniqueHom (fun H ↦ StructuredArrow.homMk
      (G.descOfIsLeftKanExtension (α ≫ whiskerLeft γ β ≫ (associator γ γ' G).inv) H.right
        (α ≫ whiskerLeft γ H.hom ≫ (associator _ _ _).inv)) ?_) ?_⟩⟩
    · apply F'.hom_ext_of_isLeftKanExtension α
      ext X
      have := congr_app (G.descOfIsLeftKanExtension_fac
        (α ≫ whiskerLeft γ β ≫ (associator γ γ' G).inv) H.right
        (α ≫ whiskerLeft γ H.hom ≫ (associator _ _ _).inv)) X
      dsimp at this ⊢
      simpa using this
    · intro H m
      have hm := StructuredArrow.w m
      refine StructuredArrow.hom_ext _ _ ?_
      dsimp
      apply G.hom_ext_of_isLeftKanExtension (α ≫ whiskerLeft γ β ≫ (associator γ γ' G).inv)
      rw [descOfIsLeftKanExtension_fac]
      ext X
      have := congr_app hm (γ.obj X)
      dsimp at this ⊢
      simp [← this]

/-- **Proposition 4.3.3(2).** If `(F', α)` is a left Kan extension of `u` along
`γ`, then a left Kan extension of `F'` along `γ'` exists iff one of `u` along
`γ'γ` does. -/
theorem hasLeftKanExtension_comp_iff {F' : A' ⥤ C} (α : u ⟶ γ ⋙ F')
    [F'.IsLeftKanExtension α] :
    HasLeftKanExtension γ' F' ↔ HasLeftKanExtension (γ ⋙ γ') u := by
  constructor
  · intro _
    have := (isLeftKanExtension_comp_iff α (γ'.leftKanExtensionUnit F')).1 inferInstance
    exact HasLeftKanExtension.mk _ (α ≫ whiskerLeft γ (γ'.leftKanExtensionUnit F') ≫
      (associator γ γ' _).inv)
  · intro _
    let β := F'.descOfIsLeftKanExtension α (γ' ⋙ (γ ⋙ γ').leftKanExtension u)
      ((γ ⋙ γ').leftKanExtensionUnit u ≫ (associator _ _ _).hom)
    have h : α ≫ whiskerLeft γ β ≫ (associator γ γ' _).inv =
        (γ ⋙ γ').leftKanExtensionUnit u := by
      ext X
      simp [β]
    have := (isLeftKanExtension_comp_iff α β).2 (by rw [h]; infer_instance)
    exact HasLeftKanExtension.mk _ β

end Composition

section Equivalence

variable {A' : Type u₃} [Category.{v₃} A'] {A'' : Type*} [Category A'']
  {C : Type*} [Category C] {γ : A ⥤ A'} (e : A' ≌ A'') {u : A ⥤ C}

/-- **Corollary 4.3.4(1)**, existence. A right Kan extension of `u` along `γ`
exists iff one along `γ` followed by an equivalence does. -/
theorem hasRightKanExtension_comp_equivalence_iff :
    HasRightKanExtension (γ ⋙ e.functor) u ↔ HasRightKanExtension γ u :=
  hasRightExtension_iff_postcomp₁ (Iso.refl _) u

/-- **Corollary 4.3.4(1)**, comparison: `(F', α)` is a right Kan extension along
`γ` iff `(F' ∘ e⁻¹, α ⋆ ψ)` is one along `eγ`. -/
theorem isRightKanExtension_comp_equivalence_iff {F' : A' ⥤ C} (α : γ ⋙ F' ⟶ u) :
    F'.IsRightKanExtension α ↔ (e.inverse ⋙ F').IsRightKanExtension
      ((associator _ _ _).inv ≫
        whiskerRight (associator γ e.functor e.inverse ≪≫ isoWhiskerLeft γ e.unitIso.symm ≪≫
          γ.rightUnitor).hom F' ≫ α) :=
  isRightKanExtension_iff_postcomp₁ e.inverse _ α

/-- **Corollary 4.3.4(2)**, existence. -/
theorem hasLeftKanExtension_comp_equivalence_iff :
    HasLeftKanExtension (γ ⋙ e.functor) u ↔ HasLeftKanExtension γ u :=
  hasLeftExtension_iff_postcomp₁ (Iso.refl _) u

/-- **Corollary 4.3.4(2)**, comparison. -/
theorem isLeftKanExtension_comp_equivalence_iff {F' : A' ⥤ C} (α : u ⟶ γ ⋙ F') :
    F'.IsLeftKanExtension α ↔ (e.inverse ⋙ F').IsLeftKanExtension
      (α ≫ whiskerRight (associator γ e.functor e.inverse ≪≫
        isoWhiskerLeft γ e.unitIso.symm ≪≫ γ.rightUnitor).inv F' ≫ (associator _ _ _).hom) :=
  isLeftKanExtension_iff_postcomp₁ e.inverse _ α

end Equivalence

end ABCCofibrations
