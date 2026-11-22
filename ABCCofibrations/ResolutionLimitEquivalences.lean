/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ResolutionColimitEquivalences
public import ABCCofibrations.FibrationCategory

/-! # Proposition 9.5.4(2), by duality

Let `M` be a fibration category, that is `ABCCofibrationCategory Mᵒᵖ`, and let
`X` be a Reedy fibrant diagram on the inverse resolution
`Δ′ᵒᵖD = (Δ′(Dᵒᵖ))ᵒᵖ`. Then `X.rightOp : Δ′(Dᵒᵖ) ⥤ Mᵒᵖ` is Reedy cofibrant, so
Proposition 9.5.4(1) applies to it in `Mᵒᵖ`. Here "restricted" means that
`X.rightOp` is restricted: `X` inverts the maps whose initial component is an
identity.

The relative limits `lim_{pᵢ} X` are the opposites of the relative colimits of
`X.rightOp` in `Mᵒᵖ`, and the statements below are phrased that way.

The step from `IsReedyFibrant X` (Reedy cofibrancy of `X.op` on the double
opposite) to Reedy cofibrancy of `X.rightOp` is `isReedyCofibrant_opOp_comp`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory Limits Opposite HomotopicalAlgebra
namespace ABCCofibrations

section OpOp

variable {C : Type*} [Category C] {N : Type*} [Category N] [CategoryWithCofibrations N]
  [CategoryWithWeakEquivalences N] [HasInitial N] [ABCPrecofibrationCategory N]

/-- The latching category of `c` maps isomorphically to that of `op (op c)`. -/
def latchingOpOp (c : C) : LatchingCategory c ⥤ LatchingCategory (op (op c)) where
  obj k := ⟨Over.mk k.obj.hom.op.op, fun h ↦ k.property (congrArg (fun x ↦ x.unop.unop) h)⟩
  map {k k'} φ := ⟨Over.homMk φ.hom.left.op.op (by
    change (φ.hom.left ≫ k'.obj.hom).op.op = _
    rw [Over.w φ.hom]
    rfl)⟩

instance (c : C) : (latchingOpOp c).Full where
  map_surjective {k k'} φ := ⟨⟨Over.homMk
    (show k.obj.left ⟶ k'.obj.left from φ.hom.left.unop.unop) (by
    apply Quiver.Hom.op_inj
    apply Quiver.Hom.op_inj
    exact Over.w φ.hom)⟩, rfl⟩

instance (c : C) : (latchingOpOp c).Faithful where
  map_injective {k k'} φ ψ h := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    have := congrArg (fun χ ↦ χ.hom.left) h
    change φ.hom.left.op.op = ψ.hom.left.op.op at this
    exact Quiver.Hom.op_inj (Quiver.Hom.op_inj this)

instance (c : C) : (latchingOpOp c).EssSurj where
  mem_essImage k := ⟨⟨Over.mk k.obj.hom.unop.unop,
    fun h ↦ k.property (congrArg (fun x ↦ op (op x)) h)⟩, ⟨eqToIso (by rfl)⟩⟩

instance (c : C) : (latchingOpOp c).IsEquivalence where

/-- Reedy cofibrancy transfers from `Cᵒᵖᵒᵖ` to `C`. -/
theorem isReedyCofibrant_opOp_comp (X : Cᵒᵖᵒᵖ ⥤ N) [∀ c, HasColimit (latchingDiagram X c)]
    (hX : IsReedyCofibrant X) :
    ∃ _ : ∀ c, HasColimit (latchingDiagram (opOp C ⋙ X) c),
      IsReedyCofibrant (opOp C ⋙ X) := by
  have hC (c : C) : HasColimit (latchingDiagram (opOp C ⋙ X) c) :=
    Functor.Final.comp_hasColimit (latchingOpOp c) (G := latchingDiagram X (op (op c)))
  refine ⟨hC, fun c ↦ ?_⟩
  have : HasColimit (latchingOpOp c ⋙ latchingDiagram X (op (op c))) := hC c
  obtain ⟨hL, hi⟩ := hX (op (op c))
  exact transfer_desc (latchingOpOp c) (latchingDiagram X (op (op c)))
    (latchingCocone X (op (op c))) hL hi

end OpOp

variable {D : Type} [SmallCategory D]
variable {M : Type u} [Category.{v} M] [CategoryWithFibrations M]
  [CategoryWithWeakEquivalences M] [HasTerminal M] [ABCFibrationCategory.{0} M]

/-- A Reedy fibrant diagram on the inverse resolution gives a Reedy cofibrant
diagram on Δ′(Dᵒᵖ) in `Mᵒᵖ`. -/
theorem isReedyCofibrant_rightOp_of_isReedyFibrant (X : CosemisimplicialResolution D ⥤ M)
    [∀ c, HasColimit (latchingDiagram X.op c)] (hX : IsReedyFibrant X) :
    ∃ _ : ∀ c, HasColimit (latchingDiagram X.rightOp c), IsReedyCofibrant X.rightOp :=
  isReedyCofibrant_opOp_comp X.op hX

/-- **Proposition 9.5.4(2), key step.** For Reedy fibrant `X` on Δ′ᵒᵖD whose
`rightOp` is restricted, the map `(lim_{(d ↓ pᵢ)} X) ⟶ X_(d)` (the `unop` of a
colimit inclusion in `Mᵒᵖ`) is a weak equivalence. -/
theorem weakEquivalence_coresolution_limit_π (X : CosemisimplicialResolution D ⥤ M)
    [∀ c, HasColimit (latchingDiagram X.op c)] (hXR : IsReedyFibrant X)
    (hX : IsResolutionRestricted X.rightOp) (d : D) :
    ∃ _ : HasColimit (resolutionCommaDiagram (op d) X.rightOp),
      WeakEquivalence (colimit.ι (resolutionCommaDiagram (op d) X.rightOp)
        (resolutionSliceCenter (op d))).unop := by
  obtain ⟨hL, hR⟩ := isReedyCofibrant_rightOp_of_isReedyFibrant X hXR
  obtain ⟨h, hw⟩ := weakEquivalence_resolutionComma_colimit_ι (op d) X.rightOp hR hX
  exact ⟨h, (weakEquivalences_unop_iff _).2 hw⟩

/-- **Proposition 9.5.4(2)(b).** For Reedy fibrant `X, X′` on Δ′ᵒᵖD with
restricted `rightOp`s, a map `f : X ⟶ X′` is a pointwise weak equivalence iff the
induced maps of relative limits are weak equivalences. -/
theorem coresolution_limMap_weakEquivalence_iff (X X' : CosemisimplicialResolution D ⥤ M)
    [∀ c, HasColimit (latchingDiagram X.op c)] [∀ c, HasColimit (latchingDiagram X'.op c)]
    (hXR : IsReedyFibrant X) (hX'R : IsReedyFibrant X')
    (hX : IsResolutionRestricted X.rightOp) (hX' : IsResolutionRestricted X'.rightOp)
    (f : X ⟶ X') :
    ∃ (_ : ∀ d, HasColimit (resolutionCommaDiagram d X'.rightOp))
      (_ : ∀ d, HasColimit (resolutionCommaDiagram d X.rightOp)),
      ((∀ x, WeakEquivalence (f.app x)) ↔
        ∀ d, WeakEquivalence (colimMap (Functor.whiskerLeft
          (CostructuredArrow.proj (resolutionTerminal Dᵒᵖ ⋙ 𝟭 Dᵒᵖ) d)
            (NatTrans.rightOp f))).unop) := by
  obtain ⟨hL, hR⟩ := isReedyCofibrant_rightOp_of_isReedyFibrant X hXR
  obtain ⟨hL', hR'⟩ := isReedyCofibrant_rightOp_of_isReedyFibrant X' hX'R
  obtain ⟨hc', hc, hiff⟩ :=
    resolution_colimMap_weakEquivalence_iff X'.rightOp X.rightOp hR' hR hX' hX (NatTrans.rightOp f)
  refine ⟨hc', hc, ?_⟩
  constructor
  · intro hf d
    refine (weakEquivalences_unop_iff _).2 (hiff.1 (fun x ↦ ?_) d)
    exact (weakEquivalences_op_iff (f.app (op x))).2 (hf (op x))
  · intro hd x
    have := hiff.2 (fun d ↦ (weakEquivalences_unop_iff _).1 (hd d)) x.unop
    exact (weakEquivalences_op_iff (f.app x)).1 this

/-- The dual of `f : pᵢ* Y ⟶ X` as a map `X.rightOp ⟶ pₜ* Y.op` in `Mᵒᵖ`. -/
def coresolutionAdjointDual {X : CosemisimplicialResolution D ⥤ M} {Y : D ⥤ M}
    (f : resolutionInitial D ⋙ Y ⟶ X) : X.rightOp ⟶ resolutionTerminal Dᵒᵖ ⋙ Y.op :=
  NatTrans.rightOp f

/-- **Proposition 9.5.4(2)(a).** For Reedy fibrant `X` on Δ′ᵒᵖD with restricted
`rightOp`, a map `f : pᵢ* Y ⟶ X` is a pointwise weak equivalence iff all its
adjoint maps `Y_d ⟶ lim_{(d ↓ pᵢ)} X` are weak equivalences. -/
theorem coresolution_adjoint_weakEquivalence_iff (X : CosemisimplicialResolution D ⥤ M)
    [∀ c, HasColimit (latchingDiagram X.op c)] (hXR : IsReedyFibrant X)
    (hX : IsResolutionRestricted X.rightOp) {Y : D ⥤ M} (f : resolutionInitial D ⋙ Y ⟶ X) :
    ∃ _ : ∀ d, HasColimit (resolutionCommaDiagram d X.rightOp),
      ((∀ x, WeakEquivalence (f.app x)) ↔
        ∀ d, WeakEquivalence
          (colimit.desc _ (resolutionAdjointCocone (coresolutionAdjointDual f) d)).unop) := by
  obtain ⟨hL, hR⟩ := isReedyCofibrant_rightOp_of_isReedyFibrant X hXR
  obtain ⟨hc, hiff⟩ := resolution_adjoint_weakEquivalence_iff X.rightOp hR hX
    (coresolutionAdjointDual f)
  refine ⟨hc, ?_⟩
  constructor
  · intro hf d
    refine (weakEquivalences_unop_iff _).2 (hiff.1 (fun x ↦ ?_) d)
    exact (weakEquivalences_op_iff (f.app (op x))).2 (hf (op x))
  · intro hd x
    have := hiff.2 (fun d ↦ (weakEquivalences_unop_iff _).1 (hd d)) x.unop
    exact (weakEquivalences_op_iff (f.app x)).1 this

end ABCCofibrations
