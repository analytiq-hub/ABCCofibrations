/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.DegreeColimits

/-! # Gluing diagrams on degree truncations

Adjacent restriction isomorphisms extend to coherent comparisons between
any two stages. They allow the diagrams to be assembled objectwise using
the first stage containing each object. No colimit is required.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory Limits
namespace ABCCofibrations.DegreeDiagramGluing
variable {D : Type w} [SmallCategory D] (deg : D → ℕ)
  {M : Type u} [Category.{v} M]
  (S : ∀ n, (degreeBelow deg n).FullSubcategory ⥤ M)
  (step : ∀ n, degreeInclusion deg (Nat.le_succ n) ⋙ S (n + 1) ≅ S n)

/-- The coherent comparison from any later stage to an earlier restriction. -/
noncomputable def comparison {n m : ℕ} (h : n ≤ m) : degreeInclusion deg h ⋙ S m ≅ S n :=
  Nat.leRec (Iso.refl _) (fun {k} h e ↦
    (Functor.isoWhiskerLeft (degreeInclusion deg h) (step k)).trans e) h

@[simp]
lemma comparison_refl (n : ℕ) : comparison deg S step (le_refl n) = Iso.refl (S n) := by
  rw [comparison, Nat.leRec_self]
  ext d
  rfl

lemma comparison_succ {n m : ℕ} (h : n ≤ m) :
    comparison deg S step (Nat.le_trans h (Nat.le_succ m)) =
      (Functor.isoWhiskerLeft (degreeInclusion deg h) (step m)).trans
        (comparison deg S step h) := by
  unfold comparison
  exact Nat.leRec_succ _ _ h

/-- Comparison maps satisfy the cocycle identity. -/
lemma comparison_trans {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    comparison deg S step (h.trans h') =
      (Functor.isoWhiskerLeft (degreeInclusion deg h) (comparison deg S step h')).trans
        (comparison deg S step h) := by
  induction k, h' using Nat.le_induction with
  | base =>
    ext e
    simp
  | succ k hk ih =>
    rw [comparison_succ deg S step (h.trans hk), ih, comparison_succ deg S step hk]
    ext e
    simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc]
    rfl

/-- Values are taken at the first truncation containing the object. -/
noncomputable def obj (d : D) : M := (S (deg d + 1)).obj ⟨d, Nat.lt_succ_self _⟩

variable (hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b)

/-- An arrow is evaluated in the first stage containing its target. -/
noncomputable def map {a b : D} (f : a ⟶ b) : obj deg S a ⟶ obj deg S b :=
  (comparison deg S step (Nat.succ_le_succ (hmono f))).inv.app ⟨a, Nat.lt_succ_self _⟩ ≫
    (S (deg b + 1)).map
      (⟨f⟩ : (⟨a, lt_of_le_of_lt (hmono f) (Nat.lt_succ_self _)⟩ :
        (degreeBelow deg (deg b + 1)).FullSubcategory) ⟶ ⟨b, Nat.lt_succ_self _⟩)

lemma map_id (d : D) : map deg S step hmono (𝟙 d) = 𝟙 _ := by
  dsimp only [map]
  rw [comparison_refl]
  change 𝟙 _ ≫ (S (deg d + 1)).map (𝟙 _) = 𝟙 _
  simp

lemma map_comp {a b c : D} (f : a ⟶ b) (g : b ⟶ c) :
    map deg S step hmono (f ≫ g) = map deg S step hmono f ≫ map deg S step hmono g := by
  let hab := Nat.succ_le_succ (hmono f)
  let hbc := Nat.succ_le_succ (hmono g)
  let eab := comparison deg S step hab
  let ebc := comparison deg S step hbc
  have hcmp := congrArg (fun e ↦ e.inv.app (⟨a, Nat.lt_succ_self _⟩ :
    (degreeBelow deg (deg a + 1)).FullSubcategory)) (comparison_trans deg S step hab hbc)
  change (comparison deg S step (hab.trans hbc)).inv.app _ =
    eab.inv.app _ ≫ ebc.inv.app _ at hcmp
  dsimp only [map]
  rw [hcmp]
  have hn := ebc.inv.naturality
    (⟨f⟩ : (⟨a, lt_of_le_of_lt (hmono f) (Nat.lt_succ_self _)⟩ :
      (degreeBelow deg (deg b + 1)).FullSubcategory) ⟶ ⟨b, Nat.lt_succ_self _⟩)
  change (S (deg b + 1)).map _ ≫ ebc.inv.app _ = ebc.inv.app _ ≫
    (S (deg c + 1)).map _ at hn
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp]
  rfl

/-- The assembled whole diagram. -/
noncomputable def diagram : D ⥤ M where
  obj := obj deg S
  map := map deg S step hmono
  map_id := map_id deg S step hmono
  map_comp := map_comp deg S step hmono

/-- Its restriction to each stage is canonically isomorphic to that stage. -/
noncomputable def restrictionIso (n : ℕ) :
    (degreeBelow deg n).ι ⋙ diagram deg S step hmono ≅ S n :=
  NatIso.ofComponents
    (fun d ↦ (comparison deg S step (show deg d.obj + 1 ≤ n from d.property)).symm.app
      ⟨d.obj, Nat.lt_succ_self _⟩)
    (fun {a b} f ↦ by
      let hab := Nat.succ_le_succ (hmono f.hom)
      let hbn : deg b.obj + 1 ≤ n := b.property
      have hcmp := congrArg (fun e ↦ e.inv.app (⟨a.obj, Nat.lt_succ_self _⟩ :
        (degreeBelow deg (deg a.obj + 1)).FullSubcategory))
        (comparison_trans deg S step hab hbn)
      change _ = (comparison deg S step hab).inv.app _ ≫
        (comparison deg S step hbn).inv.app _ at hcmp
      change map deg S step hmono f.hom ≫
        (comparison deg S step hbn).inv.app ⟨b.obj, Nat.lt_succ_self _⟩ =
          (comparison deg S step (hab.trans hbn)).inv.app ⟨a.obj, Nat.lt_succ_self _⟩ ≫
            (S n).map f
      dsimp only [map]
      rw [hcmp]
      have hn := (comparison deg S step hbn).inv.naturality
        (⟨f.hom⟩ : (⟨a.obj, lt_of_le_of_lt (hmono f.hom) (Nat.lt_succ_self _)⟩ :
          (degreeBelow deg (deg b.obj + 1)).FullSubcategory) ⟶ ⟨b.obj, Nat.lt_succ_self _⟩)
      simp only [Category.assoc]
      erw [hn]
      rfl)

section Left
variable (X : D ⥤ M) (a : ∀ n, (degreeBelow deg n).ι ⋙ X ⟶ S n)
  (ha : ∀ n, Functor.whiskerLeft (degreeInclusion deg (Nat.le_succ n)) (a (n + 1)) ≫
    (step n).hom = a n)

include ha in
/-- Compatibility with the left maps propagates to every comparison. -/
lemma comparison_left {n m : ℕ} (h : n ≤ m) :
    Functor.whiskerLeft (degreeInclusion deg h) (a m) ≫
      (comparison deg S step h).hom = a n := by
  induction m, h using Nat.le_induction with
  | base =>
    ext d
    simp only [comparison_refl, Iso.refl_hom, NatTrans.comp_app,
      NatTrans.id_app, Functor.whiskerLeft_app]
    change (a n).app d ≫ 𝟙 _ = (a n).app d
    rw [Category.comp_id]
  | succ m h ih =>
    rw [comparison_succ deg S step h]
    ext d
    change (a (m + 1)).app ((degreeInclusion deg (h.trans (Nat.le_succ m))).obj d) ≫
      (step m).hom.app ((degreeInclusion deg h).obj d) ≫
        (comparison deg S step h).hom.app d = (a n).app d
    rw [← Category.assoc]
    have hs := congrArg (fun t ↦ t.app ((degreeInclusion deg h).obj d)) (ha m)
    change (a (m + 1)).app ((degreeInclusion deg (h.trans (Nat.le_succ m))).obj d) ≫
      (step m).hom.app ((degreeInclusion deg h).obj d) =
        (a m).app ((degreeInclusion deg h).obj d) at hs
    rw [hs]
    exact congrArg (fun t ↦ t.app d) ih

include ha in
/-- Assemble compatible left maps into a natural transformation on the whole category. -/
noncomputable def lift : X ⟶ diagram deg S step hmono where
  app d := (a (deg d + 1)).app ⟨d, Nat.lt_succ_self _⟩
  naturality b d f := by
    let h := Nat.succ_le_succ (hmono f)
    have hi := congrArg (fun t ↦ t.app (⟨b, Nat.lt_succ_self _⟩ :
      (degreeBelow deg (deg b + 1)).FullSubcategory)) (comparison_left deg S step X a ha h)
    change (a (deg d + 1)).app _ ≫ (comparison deg S step h).hom.app _ =
      (a (deg b + 1)).app _ at hi
    change X.map f ≫ (a (deg d + 1)).app ⟨d, Nat.lt_succ_self _⟩ =
      (a (deg b + 1)).app ⟨b, Nat.lt_succ_self _⟩ ≫ map deg S step hmono f
    dsimp only [map]
    rw [← hi]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    exact (a (deg d + 1)).naturality
      (⟨f⟩ : (⟨b, lt_of_le_of_lt (hmono f) (Nat.lt_succ_self _)⟩ :
        (degreeBelow deg (deg d + 1)).FullSubcategory) ⟶ ⟨d, Nat.lt_succ_self _⟩)

/-- The assembled left map agrees with every stage under the restriction isomorphism. -/
lemma lift_restriction (n : ℕ) :
    Functor.whiskerLeft (degreeBelow deg n).ι (lift deg S step hmono X a ha) ≫
      (restrictionIso deg S step hmono n).hom = a n := by
  ext d
  have hi := congrArg (fun t ↦ t.app (⟨d.obj, Nat.lt_succ_self _⟩ :
    (degreeBelow deg (deg d.obj + 1)).FullSubcategory))
      (comparison_left deg S step X a ha (show deg d.obj + 1 ≤ n from d.property))
  let h : deg d.obj + 1 ≤ n := d.property
  change (a n).app d ≫ (comparison deg S step h).hom.app ⟨d.obj, Nat.lt_succ_self _⟩ =
    (a (deg d.obj + 1)).app ⟨d.obj, Nat.lt_succ_self _⟩ at hi
  change (a (deg d.obj + 1)).app ⟨d.obj, Nat.lt_succ_self _⟩ ≫
    (comparison deg S step h).inv.app ⟨d.obj, Nat.lt_succ_self _⟩ = (a n).app d
  rw [← hi]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

end Left

section Right
variable (Y : D ⥤ M) (r : ∀ n, S n ⟶ (degreeBelow deg n).ι ⋙ Y)
  (hr : ∀ n, (step n).inv ≫
    Functor.whiskerLeft (degreeInclusion deg (Nat.le_succ n)) (r (n + 1)) = r n)

include hr in
/-- Compatibility with the right maps propagates to every comparison. -/
lemma comparison_right {n m : ℕ} (h : n ≤ m) :
    (comparison deg S step h).inv ≫
      Functor.whiskerLeft (degreeInclusion deg h) (r m) = r n := by
  induction m, h using Nat.le_induction with
  | base =>
    ext d
    simp only [comparison_refl, Iso.refl_inv, Category.id_comp, Functor.whiskerLeft_app]
    rfl
  | succ m h ih =>
    rw [comparison_succ deg S step h]
    ext d
    change ((comparison deg S step h).inv.app d ≫
      (step m).inv.app ((degreeInclusion deg h).obj d)) ≫
        (r (m + 1)).app _ = (r n).app d
    rw [Category.assoc]
    have hs := congrArg (fun t ↦ t.app ((degreeInclusion deg h).obj d)) (hr m)
    change (step m).inv.app ((degreeInclusion deg h).obj d) ≫
      (r (m + 1)).app _ = (r m).app ((degreeInclusion deg h).obj d) at hs
    rw [hs]
    exact congrArg (fun t ↦ t.app d) ih

include hr in
/-- Assemble compatible right maps into a natural transformation on the whole category. -/
noncomputable def desc : diagram deg S step hmono ⟶ Y where
  app d := (r (deg d + 1)).app ⟨d, Nat.lt_succ_self _⟩
  naturality b d f := by
    let h := Nat.succ_le_succ (hmono f)
    have hi := congrArg (fun t ↦ t.app (⟨b, Nat.lt_succ_self _⟩ :
      (degreeBelow deg (deg b + 1)).FullSubcategory)) (comparison_right deg S step Y r hr h)
    change (comparison deg S step h).inv.app _ ≫ (r (deg d + 1)).app _ =
      (r (deg b + 1)).app _ at hi
    change map deg S step hmono f ≫ (r (deg d + 1)).app _ =
      (r (deg b + 1)).app _ ≫ Y.map f
    dsimp only [map]
    have hn := (r (deg d + 1)).naturality
      (⟨f⟩ : (⟨b, lt_of_le_of_lt (hmono f) (Nat.lt_succ_self _)⟩ :
        (degreeBelow deg (deg d + 1)).FullSubcategory) ⟶ ⟨d, Nat.lt_succ_self _⟩)
    change (S (deg d + 1)).map
      (⟨f⟩ : (⟨b, lt_of_le_of_lt (hmono f) (Nat.lt_succ_self _)⟩ :
        (degreeBelow deg (deg d + 1)).FullSubcategory) ⟶ ⟨d, Nat.lt_succ_self _⟩) ≫
      (r (deg d + 1)).app ⟨d, Nat.lt_succ_self _⟩ =
        (r (deg d + 1)).app ⟨b, lt_of_le_of_lt (hmono f) (Nat.lt_succ_self _)⟩ ≫ Y.map f at hn
    rw [Category.assoc, hn, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ Y.map f) hi

/-- The assembled right map agrees with every stage under the restriction isomorphism. -/
lemma desc_restriction (n : ℕ) :
    (restrictionIso deg S step hmono n).inv ≫
      Functor.whiskerLeft (degreeBelow deg n).ι (desc deg S step hmono Y r hr) = r n := by
  ext d
  have hi := congrArg (fun t ↦ t.app (⟨d.obj, Nat.lt_succ_self _⟩ :
    (degreeBelow deg (deg d.obj + 1)).FullSubcategory))
      (comparison_right deg S step Y r hr (show deg d.obj + 1 ≤ n from d.property))
  let h : deg d.obj + 1 ≤ n := d.property
  change (comparison deg S step h).inv.app ⟨d.obj, Nat.lt_succ_self _⟩ ≫ (r n).app d =
    (r (deg d.obj + 1)).app ⟨d.obj, Nat.lt_succ_self _⟩ at hi
  change (comparison deg S step h).hom.app ⟨d.obj, Nat.lt_succ_self _⟩ ≫
    (r (deg d.obj + 1)).app ⟨d.obj, Nat.lt_succ_self _⟩ = (r n).app d
  rw [← hi]
  simp

end Right

end ABCCofibrations.DegreeDiagramGluing
