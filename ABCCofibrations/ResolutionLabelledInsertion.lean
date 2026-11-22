/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ResolutionVertexInsertion

/-! # Labelled terminal-vertex insertion on Δ′D

For a category `D` with a specified terminal object `t`, appending `t` as a new
final vertex is an endofunctor of the direct resolution Δ′D. It receives
natural maps from the identity (include the old vertices) and from the
constant singleton functor at `t` (select the new vertex):

  𝟭 ⟶ resolutionAppend ⟵ const (resolutionSingleton t).

This is the labelled form of the vertex-insertion zigzag of
`SemisimplexContraction.lean`, now inserting at the end so that the label of
the new vertex receives maps from all the others; compare Szumiło,
arXiv:1411.0303v1, Lemma 3.9. No initial object of Δ′D is asserted, and none is
used. The inverse-side statement for an initial object follows by duality.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory Limits Opposite
namespace ABCCofibrations

/-! ### Appending a final vertex to ordinals -/

/-- Extend an ordinal embedding by sending the new final vertex to the new final vertex. -/
def semisimplexAppendFun {n m : SemiSimplexCategory} (f : n ⟶ m) :
    Fin (n.len + 2) → Fin (m.len + 2) :=
  Fin.lastCases (Fin.last _) (fun i ↦ (SemiSimplexCategory.homEquiv f i).castSucc)

@[simp] theorem semisimplexAppendFun_last {n m : SemiSimplexCategory} (f : n ⟶ m) :
    semisimplexAppendFun f (Fin.last _) = Fin.last _ := by
  simp [semisimplexAppendFun]

@[simp] theorem semisimplexAppendFun_castSucc {n m : SemiSimplexCategory} (f : n ⟶ m)
    (i : Fin (n.len + 1)) :
    semisimplexAppendFun f i.castSucc = (SemiSimplexCategory.homEquiv f i).castSucc := by
  simp [semisimplexAppendFun]

theorem semisimplexAppendFun_strictMono {n m : SemiSimplexCategory} (f : n ⟶ m) :
    StrictMono (semisimplexAppendFun f) := by
  intro a b h
  induction b using Fin.lastCases with
  | last =>
    induction a using Fin.lastCases with
    | last => exact absurd h (lt_irrefl _)
    | cast i => simp
  | cast j =>
    induction a using Fin.lastCases with
    | last => exact absurd h (not_lt.2 (Fin.le_last _))
    | cast i =>
      simpa using (SemiSimplexCategory.homEquiv f).strictMono
        (Fin.castSucc_lt_castSucc_iff.mp h)

/-- Extend an ordinal embedding by a new final vertex. -/
def semisimplexAppendMap {n m : SemiSimplexCategory} (f : n ⟶ m) :
    SemiSimplexCategory.mk (n.len + 1) ⟶ SemiSimplexCategory.mk (m.len + 1) :=
  SemiSimplexCategory.homEquiv.symm
    (OrderEmbedding.ofStrictMono _ (semisimplexAppendFun_strictMono f))

@[simp] theorem homEquiv_semisimplexAppendMap {n m : SemiSimplexCategory} (f : n ⟶ m)
    (i : Fin (n.len + 2)) :
    SemiSimplexCategory.homEquiv (semisimplexAppendMap f) i = semisimplexAppendFun f i := by
  simp [semisimplexAppendMap]

/-- Adjoin a new final vertex to every ordinal. -/
def semisimplexAppend : SemiSimplexCategory ⥤ SemiSimplexCategory where
  obj n := ⟨n.len + 1⟩
  map := semisimplexAppendMap
  map_id n := by
    apply SemiSimplexCategory.hom_ext
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  map_comp f g := by
    apply SemiSimplexCategory.hom_ext
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp

/-- Include all original vertices before the new final vertex. -/
def semisimplexToAppend : 𝟭 SemiSimplexCategory ⟶ semisimplexAppend where
  app n := SemiSimplexCategory.homEquiv.symm (Fin.castSuccOrderEmb (n := n.len + 1))
  naturality n m f := by
    apply SemiSimplexCategory.hom_ext
    ext i
    simp [semisimplexAppend]

/-- Select the newly adjoined final vertex, naturally in the ordinal. -/
def semisimplexPointToAppend :
    (Functor.const SemiSimplexCategory).obj (SemiSimplexCategory.mk 0) ⟶
      semisimplexAppend where
  app n := SemiSimplexCategory.homEquiv.symm
    (OrderEmbedding.ofStrictMono (fun _ ↦ Fin.last (n.len + 1))
      (fun i j h ↦ by fin_cases i; fin_cases j; simp at h))
  naturality n m f := by
    apply SemiSimplexCategory.hom_ext
    ext i
    fin_cases i
    simp [semisimplexAppend]

/-! ### Label compatibility of `appendTerminal` -/

section Labels

variable {C : Type u} [Category.{v} C] {c : C} (hc : IsTerminal c)

theorem comp_finAppendTerminal_of_castSucc {J : Type*} [Category J] {m : ℕ}
    (F' : J ⥤ Fin (m + 2)) (F : J ⥤ Fin (m + 1))
    (h : ∀ j, F'.obj j = (F.obj j).castSucc) :
    F' ⋙ finAppendTerminal m = F ⋙ WithTerminal.incl :=
  CategoryTheory.Functor.ext (fun j ↦ by simp [finAppendTerminal, finAppendTerminalObj, h]; rfl)
    (fun _ _ _ ↦ Subsingleton.elim _ _)

theorem incl_liftToTerminal {J : Type*} [Category J] (Y : J ⥤ C) :
    WithTerminal.incl ⋙ WithTerminal.liftToTerminal Y hc = Y :=
  rfl

/-- Reindexing an appended chain along a map avoiding the new vertex forgets it. -/
theorem comp_appendTerminal_of_castSucc {J : Type*} [Category J] {m : ℕ}
    (F' : J ⥤ Fin (m + 2)) (F : J ⥤ Fin (m + 1))
    (h : ∀ j, F'.obj j = (F.obj j).castSucc) (Y : Fin (m + 1) ⥤ C) :
    F' ⋙ appendTerminal Y hc = F ⋙ Y := by
  change (F' ⋙ finAppendTerminal m) ⋙ WithTerminal.liftToTerminal Y hc = _
  rw [comp_finAppendTerminal_of_castSucc F' F h]
  rfl

theorem finAppendTerminal_comp_map {n m : ℕ}
    (F : Fin (n + 1) ⥤ Fin (m + 1)) (F' : Fin (n + 2) ⥤ Fin (m + 2))
    (hcast : ∀ i, F'.obj i.castSucc = (F.obj i).castSucc)
    (hlast : F'.obj (Fin.last (n + 1)) = Fin.last (m + 1)) :
    F' ⋙ finAppendTerminal m = finAppendTerminal n ⋙ WithTerminal.map F :=
  CategoryTheory.Functor.ext
    (fun i ↦ by
      induction i using Fin.lastCases with
      | last => simp [finAppendTerminal, finAppendTerminalObj, hlast]
      | cast i => simp [finAppendTerminal, finAppendTerminalObj, hcast])
    (fun _ _ _ ↦ Subsingleton.elim _ _)

theorem map_liftToTerminal {J K : Type*} [Category J] [Category K]
    (F : J ⥤ K) (Y : K ⥤ C) :
    WithTerminal.map F ⋙ WithTerminal.liftToTerminal Y hc =
      WithTerminal.liftToTerminal (F ⋙ Y) hc :=
  CategoryTheory.Functor.ext (fun X ↦ by cases X <;> rfl)
    (fun X Y f ↦ by
      cases X <;> cases Y
      · simp; rfl
      · exact hc.hom_ext _ _
      · cases f
      · simp)

/-- Appending a terminal vertex commutes with reindexing along an
extended map that fixes the new vertex. -/
theorem appendTerminal_comp_of_append {n m : ℕ}
    (F : Fin (n + 1) ⥤ Fin (m + 1)) (F' : Fin (n + 2) ⥤ Fin (m + 2))
    (hcast : ∀ i, F'.obj i.castSucc = (F.obj i).castSucc)
    (hlast : F'.obj (Fin.last (n + 1)) = Fin.last (m + 1)) (Y : Fin (m + 1) ⥤ C) :
    F' ⋙ appendTerminal Y hc = appendTerminal (F ⋙ Y) hc := by
  change (F' ⋙ finAppendTerminal m) ⋙ WithTerminal.liftToTerminal Y hc =
    finAppendTerminal n ⋙ WithTerminal.liftToTerminal (F ⋙ Y) hc
  rw [finAppendTerminal_comp_map F F' hcast hlast, ← map_liftToTerminal hc F Y]
  rfl

end Labels

/-! ### The labelled insertion functor on Δ′D -/

section Resolution

variable {D : Type u} [Category.{v} D]

/-- The labels of a simplex of Δ′D, as a functor out of a finite ordinal. -/
abbrev resolutionLabel (x : SemisimplicialResolution D) :
    Fin (x.unop.obj.unop.len + 1) ⥤ D :=
  x.unop.val

/-- Morphisms of Δ′D are determined by their underlying ordinal embeddings. -/
theorem resolution_hom_ext {x y : SemisimplicialResolution D} {f g : x ⟶ y}
    (h : (resolutionOrdinal D).map f = (resolutionOrdinal D).map g) : f = g :=
  (resolutionOrdinal D).map_injective h

theorem semisimplex_toFunctor_obj {a b : SemiSimplexCategory} (g : a ⟶ b)
    (i : Fin (a.len + 1)) :
    (SimplexCategory.toCat.map (SemiSimplexCategory.toSimplexCategory.map g)).toFunctor.obj i =
      SemiSimplexCategory.homEquiv g i :=
  rfl

variable {t : D} (ht : IsTerminal t)

/-- Append the terminal object as a new final vertex of a labelled simplex. -/
def resolutionAppendObj (x : SemisimplicialResolution D) : SemisimplicialResolution D :=
  op ((semisimplicialNerve D).elementsMk (op (SemiSimplexCategory.mk (x.unop.obj.unop.len + 1)))
    (appendTerminal (resolutionLabel x) ht))

@[simp] theorem resolutionLabel_appendObj (x : SemisimplicialResolution D) :
    resolutionLabel (resolutionAppendObj ht x) = appendTerminal (resolutionLabel x) ht :=
  rfl

/-- The labels transform compatibly with the extended ordinal embedding. -/
theorem appendTerminal_nerve_map {a b : SemiSimplexCategory} (g : a ⟶ b)
    (Y : Fin (b.len + 1) ⥤ D) :
    (semisimplicialNerve D).map (semisimplexAppendMap g).op (appendTerminal Y ht) =
      appendTerminal ((semisimplicialNerve D).map g.op Y : Fin (a.len + 1) ⥤ D) ht := by
  change (SimplexCategory.toCat.map (SemiSimplexCategory.toSimplexCategory.map
      (semisimplexAppendMap g))).toFunctor ⋙ appendTerminal Y ht =
    appendTerminal ((SimplexCategory.toCat.map
      (SemiSimplexCategory.toSimplexCategory.map g)).toFunctor ⋙ Y) ht
  refine appendTerminal_comp_of_append ht _ _ (fun i ↦ ?_) ?_ Y
  · exact ((semisimplex_toFunctor_obj (semisimplexAppendMap g) i.castSucc).trans
      (by simp)).trans (congrArg Fin.castSucc (semisimplex_toFunctor_obj g i).symm)
  · exact (semisimplex_toFunctor_obj (semisimplexAppendMap g) (Fin.last _)).trans (by simp)

/-- Labelled terminal-vertex insertion: an endofunctor of Δ′D. -/
def resolutionAppend : SemisimplicialResolution D ⥤ SemisimplicialResolution D where
  obj := resolutionAppendObj ht
  map {x y} f := Quiver.Hom.op ⟨(semisimplexAppendMap f.unop.hom.unop).op, by
    refine (appendTerminal_nerve_map ht f.unop.hom.unop (resolutionLabel y)).trans ?_
    exact congrArg (appendTerminal · ht) f.unop.map_val⟩
  map_id x := resolution_hom_ext (semisimplexAppend.map_id x.unop.obj.unop)
  map_comp f g := resolution_hom_ext
    (semisimplexAppend.map_comp ((resolutionOrdinal D).map f) ((resolutionOrdinal D).map g))

/-- On underlying ordinals, labelled insertion is ordinal insertion. -/
theorem resolutionAppend_ordinal :
    resolutionAppend ht ⋙ resolutionOrdinal D = resolutionOrdinal D ⋙ semisimplexAppend :=
  rfl

@[simp] theorem resolutionOrdinal_map_append {x y : SemisimplicialResolution D} (f : x ⟶ y) :
    (resolutionOrdinal D).map ((resolutionAppend ht).map f) =
      semisimplexAppend.map ((resolutionOrdinal D).map f) :=
  rfl

/-- Every appended simplex ends at the terminal object. -/
@[simp] theorem resolutionTerminal_append (x : SemisimplicialResolution D) :
    (resolutionTerminal D).obj ((resolutionAppend ht).obj x) = t :=
  appendTerminal_obj_last (resolutionLabel x) ht

/-- The inclusion of a labelled simplex as a face of its terminal extension. -/
def resolutionToAppend : 𝟭 (SemisimplicialResolution D) ⟶ resolutionAppend ht where
  app x := Quiver.Hom.op ⟨(semisimplexToAppend.app x.unop.obj.unop).op,
    comp_appendTerminal_of_castSucc ht _ (𝟭 _) (fun i ↦
      semisimplex_toFunctor_obj _ i)
      (resolutionLabel x)⟩
  naturality _ _ f := resolution_hom_ext (semisimplexToAppend.naturality
    ((resolutionOrdinal D).map f))

/-- The new terminal vertex, as a natural map from the constant singleton. -/
def resolutionSingletonToAppend :
    (Functor.const (SemisimplicialResolution D)).obj (resolutionSingleton t) ⟶
      resolutionAppend ht where
  app x := Quiver.Hom.op ⟨(semisimplexPointToAppend.app x.unop.obj.unop).op,
    ComposableArrows.ext₀ (appendTerminal_obj_last (resolutionLabel x) ht)⟩
  naturality _ _ f := resolution_hom_ext (semisimplexPointToAppend.naturality
    ((resolutionOrdinal D).map f))

end Resolution

/-! ### The inverse side, by duality -/

section Coresolution

variable {D : Type u} [Category.{v} D] {i : D} (hi : IsInitial i)

/-- Labelled initial-vertex insertion on the inverse resolution, dual to
`resolutionAppend` for the terminal object `op i` of `Dᵒᵖ`. -/
def coresolutionPrepend : CosemisimplicialResolution D ⥤ CosemisimplicialResolution D :=
  (resolutionAppend hi.op).op

/-- Dual of `resolutionToAppend`: the projection onto the original face. -/
def coresolutionPrependToId : coresolutionPrepend hi ⟶ 𝟭 (CosemisimplicialResolution D) :=
  NatTrans.op (resolutionToAppend hi.op)

/-- Dual of `resolutionSingletonToAppend`: the projection onto the new vertex. -/
def coresolutionPrependToSingleton :
    coresolutionPrepend hi ⟶
      (Functor.const (CosemisimplicialResolution D)).obj (op (resolutionSingleton (op i))) :=
  NatTrans.op (resolutionSingletonToAppend hi.op)

end Coresolution

end ABCCofibrations
