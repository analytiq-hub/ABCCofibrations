/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.PushoutComposition
public import ABCCofibrations.SequentialColimits

/-!
# Relative pushout comparisons along sequences (Lemma 9.3.4(1))

Given a map `τ : A ⟶ B` of CF6 sequences, if every comparison map
`B_n ⊔_{A_n} A_{n+1} ⟶ B_{n+1}` is a cofibration (resp. a weak equivalence), so
is the comparison `B₀ ⊔_{A₀} colim A ⟶ colim B`.

Both parts go through the sequence `S_n = B₀ ⊔_{A₀} A_n` and the comparison maps
`φ_n : S_n ⟶ B_n`. By Lemma 9.3.3, every `φ_n` is a cofibration (resp. a weak
equivalence). The colimit of `S` is `B₀ ⊔_{A₀} colim A`, so the comparison is
`colim φ` up to this isomorphism. For weak equivalences, `colim φ` is a weak
equivalence by Lemma 1.6.4. For cofibrations, the relative latching maps of `φ`
are the given comparisons, and the Reedy argument of `ReedyStep` (the paper's
sequence `B_n ⊔_{A_n} colim A`) makes `colim φ` a cofibration.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C]

namespace RelativeSequence

variable {F G : ℕ ⥤ C} (τ : F ⟶ G)

/-- The map `A₀ ⟶ A_n`. -/
abbrev a (n : ℕ) : F.obj 0 ⟶ F.obj n := F.map (homOfLE (Nat.zero_le n))

lemma a_succ (n : ℕ) : a (F := F) n ≫ F.map (succHom n) = a (n + 1) := by
  rw [← F.map_comp]
  rfl

lemma a_zero : a (F := F) 0 = 𝟙 _ := by
  change F.map _ = _
  rw [show (homOfLE (Nat.zero_le 0) : (0 : ℕ) ⟶ 0) = 𝟙 0 from Subsingleton.elim _ _, F.map_id]

variable [∀ n, HasPushout (a (F := F) n) (τ.app 0)]

/-- `S_n = B₀ ⊔_{A₀} A_n`. -/
noncomputable def obj (n : ℕ) : C := pushout (a (F := F) n) (τ.app 0)

/-- `A_n ⟶ S_n`. -/
noncomputable def inl (n : ℕ) : F.obj n ⟶ obj τ n := pushout.inl _ _

/-- `B₀ ⟶ S_n`. -/
noncomputable def inr (n : ℕ) : G.obj 0 ⟶ obj τ n := pushout.inr _ _

lemma condition (n : ℕ) : a n ≫ inl τ n = τ.app 0 ≫ inr τ n := pushout.condition

lemma isPushout (n : ℕ) : IsPushout (a n) (τ.app 0) (inl τ n) (inr τ n) :=
  IsPushout.of_hasPushout _ _

/-- The transition `S_n ⟶ S_{n+1}`. -/
noncomputable def map (n : ℕ) : obj τ n ⟶ obj τ (n + 1) :=
  pushout.desc (F.map (succHom n) ≫ inl τ (n + 1)) (inr τ (n + 1)) (by
    rw [← Category.assoc, a_succ, condition])

@[reassoc (attr := simp)]
lemma inl_map (n : ℕ) : inl τ n ≫ map τ n = F.map (succHom n) ≫ inl τ (n + 1) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_map (n : ℕ) : inr τ n ≫ map τ n = inr τ (n + 1) :=
  pushout.inr_desc _ _ _

/-- The sequence `S`. -/
noncomputable def seq : ℕ ⥤ C := Functor.ofSequence (map τ)

lemma seq_map_succ (n : ℕ) : (seq τ).map (succHom n) = map τ n :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- `S_{n+1} = S_n ⊔_{A_n} A_{n+1}`. -/
lemma isPushout_map (n : ℕ) : IsPushout (F.map (succHom n)) (inl τ n) (inl τ (n + 1)) (map τ n) :=
  IsPushout.of_left (by rw [a_succ, inr_map]; exact isPushout τ (n + 1)) (inl_map τ n).symm
    (isPushout τ n)

/-- The comparison `φ_n : S_n ⟶ B_n`. -/
noncomputable def φ (n : ℕ) : obj τ n ⟶ G.obj n :=
  pushout.desc (τ.app n) (G.map (homOfLE (Nat.zero_le n))) (τ.naturality _)

@[reassoc (attr := simp)]
lemma inl_φ (n : ℕ) : inl τ n ≫ φ τ n = τ.app n := pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_φ (n : ℕ) : inr τ n ≫ φ τ n = G.map (homOfLE (Nat.zero_le n)) :=
  pushout.inr_desc _ _ _

lemma map_φ (n : ℕ) : map τ n ≫ φ τ (n + 1) = φ τ n ≫ G.map (succHom n) := by
  apply pushout.hom_ext
  · change inl τ n ≫ _ = inl τ n ≫ _
    rw [inl_map_assoc, inl_φ, inl_φ_assoc, τ.naturality]
  · change inr τ n ≫ _ = inr τ n ≫ _
    rw [inr_map_assoc, inr_φ, inr_φ_assoc, ← G.map_comp]
    rfl

/-- The map of sequences `φ : S ⟶ B`. -/
noncomputable def phi : seq τ ⟶ G :=
  NatTrans.ofSequence (fun n ↦ φ τ n) (fun n ↦ by
    rw [seq_map_succ]
    exact map_φ τ n)

lemma isIso_φ_zero : IsIso (φ τ 0) := by
  refine ⟨inr τ 0, ?_, ?_⟩
  · apply pushout.hom_ext
    · change inl τ 0 ≫ _ = inl τ 0 ≫ _
      rw [inl_φ_assoc, ← condition, a_zero, Category.id_comp, Category.comp_id]
    · change inr τ 0 ≫ _ = inr τ 0 ≫ _
      rw [inr_φ_assoc, show homOfLE (Nat.zero_le 0) = 𝟙 (0 : ℕ) from Subsingleton.elim _ _,
        G.map_id, Category.id_comp, Category.comp_id]
  · rw [inr_φ, show homOfLE (Nat.zero_le 0) = 𝟙 (0 : ℕ) from Subsingleton.elim _ _, G.map_id]

/-- The colimit leg `S_n ⟶ colim S`, typed with `S_n = obj τ n`. -/
noncomputable def ι' [HasColimit (seq τ)] (n : ℕ) : obj τ n ⟶ colimit (seq τ) :=
  colimit.ι (seq τ) n

@[reassoc (attr := simp)]
lemma map_ι' [HasColimit (seq τ)] (n : ℕ) : map τ n ≫ ι' τ (n + 1) = ι' τ n := by
  have := colimit.w (seq τ) (succHom n)
  rw [seq_map_succ] at this
  exact this

lemma inr_ι' [HasColimit (seq τ)] (n : ℕ) : inr τ n ≫ ι' τ n = inr τ 0 ≫ ι' τ 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← ih, ← inr_map τ n, Category.assoc, map_ι']

section Colimit

variable [HasColimit F] [HasColimit (seq τ)] {Q : C} {lQ : colimit F ⟶ Q} {rQ : G.obj 0 ⟶ Q}
  (hQ : IsPushout (colimit.ι F 0) (τ.app 0) lQ rQ)

include hQ

/-- The legs `S_n ⟶ B₀ ⊔_{A₀} colim A`. -/
noncomputable def toQ (n : ℕ) : obj τ n ⟶ Q :=
  pushout.desc (colimit.ι F n ≫ lQ) rQ (by rw [← Category.assoc, colimit.w, hQ.w])

omit [HasColimit (seq τ)] in
@[reassoc (attr := simp)]
lemma inl_toQ (n : ℕ) : inl τ n ≫ toQ τ hQ n = colimit.ι F n ≫ lQ := pushout.inl_desc _ _ _

omit [HasColimit (seq τ)] in
@[reassoc (attr := simp)]
lemma inr_toQ (n : ℕ) : inr τ n ≫ toQ τ hQ n = rQ := pushout.inr_desc _ _ _

omit [HasColimit (seq τ)] in
lemma map_toQ (n : ℕ) : map τ n ≫ toQ τ hQ (n + 1) = toQ τ hQ n := by
  apply pushout.hom_ext
  · change inl τ n ≫ map τ n ≫ toQ τ hQ (n + 1) = inl τ n ≫ toQ τ hQ n
    rw [inl_map_assoc, inl_toQ, inl_toQ, colimit.w_assoc]
  · change inr τ n ≫ map τ n ≫ toQ τ hQ (n + 1) = inr τ n ≫ toQ τ hQ n
    rw [inr_map_assoc, inr_toQ, inr_toQ]

/-- `colim S ⟶ B₀ ⊔_{A₀} colim A`. -/
noncomputable def toQ' : colimit (seq τ) ⟶ Q :=
  colimit.desc (seq τ) ⟨Q, NatTrans.ofSequence (fun n ↦ toQ τ hQ n) (fun n ↦ by
    rw [seq_map_succ]
    exact (map_toQ τ hQ n).trans (Category.comp_id _).symm)⟩

@[reassoc]
lemma ι_toQ' (n : ℕ) : ι' τ n ≫ toQ' τ hQ = toQ τ hQ n :=
  colimit.ι_desc _ n

/-- `colim A ⟶ colim S`. -/
noncomputable def fromColimit : colimit F ⟶ colimit (seq τ) :=
  colimit.desc F ⟨colimit (seq τ), NatTrans.ofSequence (fun n ↦ inl τ n ≫ ι' τ n)
    (fun n ↦ by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
      rw [← map_ι' τ n, inl_map_assoc])⟩

omit hQ in
@[reassoc]
lemma ι_fromColimit (n : ℕ) :
    colimit.ι F n ≫ fromColimit τ = inl τ n ≫ ι' τ n :=
  colimit.ι_desc _ n

/-- `B₀ ⊔_{A₀} colim A ⟶ colim S`. -/
noncomputable def fromQ : Q ⟶ colimit (seq τ) :=
  hQ.desc (fromColimit τ) (inr τ 0 ≫ ι' τ 0) (by
    rw [ι_fromColimit, ← Category.assoc, ← condition, a_zero, Category.id_comp])

lemma fromQ_toQ' : fromQ τ hQ ≫ toQ' τ hQ = 𝟙 Q := by
  apply hQ.hom_ext
  · rw [fromQ, hQ.inl_desc_assoc, Category.comp_id]
    apply colimit.hom_ext
    intro n
    rw [ι_fromColimit_assoc, ι_toQ', inl_toQ]
  · rw [fromQ, hQ.inr_desc_assoc, Category.comp_id, Category.assoc, ι_toQ', inr_toQ]

lemma toQ'_fromQ : toQ' τ hQ ≫ fromQ τ hQ = 𝟙 _ := by
  apply colimit.hom_ext
  intro n
  change ι' τ n ≫ _ = ι' τ n ≫ _
  rw [ι_toQ'_assoc, Category.comp_id]
  apply pushout.hom_ext
  · change inl τ n ≫ _ = inl τ n ≫ _
    rw [inl_toQ_assoc, fromQ, hQ.inl_desc, ι_fromColimit]
  · change inr τ n ≫ _ = inr τ n ≫ _
    rw [inr_toQ_assoc, fromQ, hQ.inr_desc]
    exact (inr_ι' τ n).symm

lemma isIso_fromQ : IsIso (fromQ τ hQ) := ⟨toQ' τ hQ, fromQ_toQ' τ hQ, toQ'_fromQ τ hQ⟩

omit hQ [HasColimit F] in
@[reassoc]
lemma ι'_colimMap_phi [HasColimit G] (n : ℕ) :
    ι' τ n ≫ colimMap (phi τ) = φ τ n ≫ colimit.ι G n :=
  ι_colimMap _ n

/-- The comparison `B₀ ⊔_{A₀} colim A ⟶ colim B` is `colim φ` up to
`fromQ`. -/
lemma comparison_eq [HasColimit G] (k : Q ⟶ colimit G) (hk₁ : lQ ≫ k = colimMap τ)
    (hk₂ : rQ ≫ k = colimit.ι G 0) : k = fromQ τ hQ ≫ colimMap (phi τ) := by
  apply hQ.hom_ext
  · rw [hk₁, fromQ, hQ.inl_desc_assoc]
    apply colimit.hom_ext
    intro n
    rw [ι_colimMap, ι_fromColimit_assoc, ι'_colimMap_phi, inl_φ_assoc]
  · rw [hk₂, fromQ, hQ.inr_desc_assoc, Category.assoc, ι'_colimMap_phi, inr_φ_assoc,
      show homOfLE (Nat.zero_le 0) = 𝟙 (0 : ℕ) from Subsingleton.elim _ _, G.map_id,
      Category.id_comp]

end Colimit

/-- The relative latching square of `φ`: `B_n ⊔_{S_n} S_{n+1}` is the pushout
`B_n ⊔_{A_n} A_{n+1}`. -/
lemma isPushout_latching (n : ℕ) {P : C} {l : F.obj (n + 1) ⟶ P} {r : G.obj n ⟶ P}
    (hP : IsPushout (F.map (succHom n)) (τ.app n) l r) :
    ∃ rS : obj τ (n + 1) ⟶ P, IsPushout (φ τ n) (map τ n) r rS ∧ inl τ (n + 1) ≫ rS = l ∧
      inr τ (n + 1) ≫ rS = G.map (homOfLE (Nat.zero_le n)) ≫ r := by
  let rS : obj τ (n + 1) ⟶ P := pushout.desc l (G.map (homOfLE (Nat.zero_le n)) ≫ r) (by
    rw [← a_succ, Category.assoc, hP.w, ← Category.assoc, τ.naturality, Category.assoc])
  have h₁ : inl τ (n + 1) ≫ rS = l := pushout.inl_desc _ _ _
  have h₂ : inr τ (n + 1) ≫ rS = G.map (homOfLE (Nat.zero_le n)) ≫ r := pushout.inr_desc _ _ _
  have p : φ τ n ≫ r = map τ n ≫ rS := by
    apply pushout.hom_ext
    · change inl τ n ≫ _ = inl τ n ≫ _
      rw [inl_φ_assoc, inl_map_assoc, h₁, hP.w]
    · change inr τ n ≫ _ = inr τ n ≫ _
      rw [inr_φ_assoc, inr_map_assoc, h₂]
  refine ⟨rS, IsPushout.of_left (by rw [inl_φ, h₁]; exact hP.flip) p (isPushout_map τ n).flip,
    h₁, h₂⟩

end RelativeSequence

section Main

variable [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [HasInitial C]
  [ABCPrecofibrationCategory C]

open RelativeSequence

/-- A cofibration-only form of `ReedyStep.map_trivial`: each transition of the
Reedy sequence is a cobase change of the relative latching map. -/
theorem ReedyStep.map_cofibration {F G : ℕ ⥤ C} (τ : F ⟶ G) [HasColimit F]
    [∀ n, IsCofibrant (F.obj n)] [IsCofibrant (colimit F)] [∀ n, Cofibration (τ.app n)]
    (n : ℕ) {P : C} {l : G.obj n ⟶ P} {r : F.obj (n + 1) ⟶ P}
    (hP : IsPushout (τ.app n) (F.map (succHom n)) l r) (k : P ⟶ G.obj (n + 1))
    (hl : l ≫ k = G.map (succHom n)) (hr : r ≫ k = τ.app (n + 1)) [Cofibration k] :
    Cofibration (ReedyStep.map τ n) := by
  have s : IsPushout (τ.app n) (F.map (succHom n) ≫ colimit.ι F (n + 1)) (ReedyStep.inl τ n)
      (ReedyStep.inr τ n) := by
    rw [colimit.w]
    exact ReedyStep.isPushout τ n
  have sq₂ := IsPushout.of_top' s hP
  set q := hP.desc (ReedyStep.inl τ n) (colimit.ι F (n + 1) ≫ ReedyStep.inr τ n) _
  have hq₁ : l ≫ q = ReedyStep.inl τ n := hP.inl_desc _ _ _
  have hq₂ : r ≫ q = colimit.ι F (n + 1) ≫ ReedyStep.inr τ n := hP.inr_desc _ _ _
  have outer : IsPushout (r ≫ k) (colimit.ι F (n + 1)) (ReedyStep.inl τ (n + 1))
      (ReedyStep.inr τ n ≫ ReedyStep.map τ n) := by
    rw [hr, ReedyStep.inr_map]
    exact ReedyStep.isPushout τ (n + 1)
  have comm : k ≫ ReedyStep.inl τ (n + 1) = q ≫ ReedyStep.map τ n := by
    apply hP.hom_ext
    · rw [reassoc_of% hl, reassoc_of% hq₁, ReedyStep.inl_map]
    · rw [reassoc_of% hr, reassoc_of% hq₂, ReedyStep.inr_map, ReedyStep.condition]
  have sq₃ : IsPushout k q (ReedyStep.inl τ (n + 1)) (ReedyStep.map τ n) :=
    IsPushout.of_left outer comm sq₂
  have := cofibration_of_isPushout hP
  have := cofibrant_target r
  have := ReedyStep.isCofibrant_obj τ n
  exact cofibration_of_isPushout sq₃

variable {F G : ℕ ⥤ C} (τ : F ⟶ G) (hF0 : IsCofibrant (F.obj 0)) (hG0 : IsCofibrant (G.obj 0))
  (hF : ∀ n, Cofibration (F.map (succHom n)))

include hF0 hG0 hF in
/-- The pushouts `S_n` exist, are cofibrant, and form a CF6 sequence. -/
private lemma prep :
    ∃ (_ : ∀ n, HasPushout (a (F := F) n) (τ.app 0)), (∀ n, IsCofibrant (obj τ n)) ∧
      ∀ n, Cofibration ((seq τ).map (succHom n)) := by
  have hFn := isCofibrant_obj_of_sequence F hF0 hF
  have ha (n : ℕ) : Cofibration (a (F := F) n) := cofibration_map_of_le F hF0 hF (Nat.zero_le n)
  have hpo (n : ℕ) : HasPushout (a (F := F) n) (τ.app 0) := hasPushout _ _
  refine ⟨hpo, fun n ↦ ?_, fun n ↦ ?_⟩
  · have := ha n
    have : Cofibration (inr τ n) := cofibration_of_isPushout (isPushout τ n)
    exact cofibrant_target (inr τ n)
  · have := ha n
    have := hF n
    have : Cofibration (inr τ n) := cofibration_of_isPushout (isPushout τ n)
    have h' : IsCofibrant (obj τ n) := cofibrant_target (inr τ n)
    have : IsCofibrant ((seq τ).obj n) := h'
    rw [seq_map_succ]
    exact cofibration_of_isPushout (isPushout_map τ n)

include hF0 hG0 hF in
/-- **Lemma 9.3.4(1)(a).** Let `τ : A ⟶ B` be a map of countable direct
sequences of cofibrations with `A₀, B₀` cofibrant. If every comparison map
`B_n ⊔_{A_n} A_{n+1} ⟶ B_{n+1}` is a cofibration, so is the comparison
`B₀ ⊔_{A₀} colim A ⟶ colim B`. The pushouts are given by arbitrary
representatives. (The paper's hypothesis that the `B`-maps are cofibrations is
not needed.) -/
theorem cofibration_sequence_comparison (h1 : SequentialCofibrationAxiom C)
    (hc : ∀ n, ∃ (P : C) (l : F.obj (n + 1) ⟶ P) (r : G.obj n ⟶ P) (c : P ⟶ G.obj (n + 1)),
      IsPushout (F.map (succHom n)) (τ.app n) l r ∧ l ≫ c = τ.app (n + 1) ∧
        r ≫ c = G.map (succHom n) ∧ Cofibration c)
    [HasColimit F] [HasColimit G] {Q : C} {lQ : colimit F ⟶ Q} {rQ : G.obj 0 ⟶ Q}
    (hQ : IsPushout (colimit.ι F 0) (τ.app 0) lQ rQ) (k : Q ⟶ colimit G)
    (hk₁ : lQ ≫ k = colimMap τ) (hk₂ : rQ ≫ k = colimit.ι G 0) : Cofibration k := by
  obtain ⟨_, hS, hs⟩ := prep τ hF0 hG0 hF
  have hFn := isCofibrant_obj_of_sequence F hF0 hF
  have ha (n : ℕ) : Cofibration (a (F := F) n) := cofibration_map_of_le F hF0 hF (Nat.zero_le n)
  have hF' := hF
  have := h1.hasColimit (seq τ) (hS 0) hs
  -- every `φ_n` is a cofibration, by Lemma 9.3.3(1)(a)
  have hφ (n : ℕ) : Cofibration (φ τ n) := by
    induction n with
    | zero =>
      have := isIso_φ_zero τ
      have := hS 0
      exact cofibration_of_isIso _
    | succ n ih =>
      obtain ⟨P, l, r, c, hP, hl, hr, hcc⟩ := hc n
      exact cofibration_comparison_comp (τ.naturality _) (isPushout τ n) hP
        (by rw [a_succ]; exact isPushout τ (n + 1)) (φ τ n) (inl_φ τ n) (inr_φ τ n)
        c hl hr (φ τ (n + 1)) (inl_φ τ (n + 1)) (by rw [inr_φ, ← G.map_comp]; rfl)
  -- the Reedy sequence of `φ`
  have : ∀ n, IsCofibrant ((seq τ).obj n) := hS
  have : IsCofibrant (colimit (seq τ)) := isCofibrant_colimit_of_sequence h1 (seq τ) (hS 0) hs
  have : ∀ n, Cofibration ((phi τ).app n) := hφ
  have hH (n : ℕ) : Cofibration ((ReedyStep.seq (phi τ)).map (succHom n)) := by
    rw [ReedyStep.seq_map_succ]
    obtain ⟨P, l, r, c, hP, hl, hr, hcc⟩ := hc n
    obtain ⟨rS, hL, h₁, h₂⟩ := isPushout_latching τ n hP
    have hrc : rS ≫ c = φ τ (n + 1) := by
      apply pushout.hom_ext
      · change inl τ (n + 1) ≫ _ = inl τ (n + 1) ≫ _
        rw [reassoc_of% h₁, hl, inl_φ]
      · change inr τ (n + 1) ≫ _ = inr τ (n + 1) ≫ _
        rw [reassoc_of% h₂, hr, ← G.map_comp, inr_φ]
        rfl
    exact ReedyStep.map_cofibration (phi τ) n (by rw [seq_map_succ]; exact hL) c hr hrc
  have hH0 := ReedyStep.isCofibrant_obj (phi τ) 0
  have := h1.hasColimit (ReedyStep.seq (phi τ)) hH0 hH
  have : Cofibration (ReedyStep.ι' (phi τ) 0) := h1.cofibration _ hH0 hH
  have : Cofibration (ReedyStep.inr (phi τ) 0) :=
    cofibration_of_isPushout (ReedyStep.isPushout (phi τ) 0)
  have : IsCofibrant (colimit (ReedyStep.seq (phi τ))) :=
    isCofibrant_colimit_of_sequence h1 _ hH0 hH
  have : Cofibration (inv (ReedyStep.φ (phi τ))) := cofibration_of_isIso _
  have hcol : Cofibration (colimMap (phi τ)) := by
    rw [show colimMap (phi τ) = (ReedyStep.inr (phi τ) 0 ≫ ReedyStep.ι' (phi τ) 0) ≫
        inv (ReedyStep.φ (phi τ)) by
        rw [← ReedyStep.colimMap_φ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
    infer_instance
  -- the comparison is `colim φ` up to an isomorphism
  have : Cofibration (colimit.ι F 0) := h1.cofibration F hF0 hF
  have : Cofibration rQ := cofibration_of_isPushout hQ
  have : IsCofibrant Q := cofibrant_target rQ
  have := isIso_fromQ τ hQ
  have : Cofibration (fromQ τ hQ) := cofibration_of_isIso _
  rw [comparison_eq τ hQ k hk₁ hk₂]
  infer_instance

include hF0 hG0 hF in
/-- **Lemma 9.3.4(1)(b).** Let `τ : A ⟶ B` be a map of countable direct
sequences of cofibrations with `A₀, B₀` cofibrant. If every comparison map
`B_n ⊔_{A_n} A_{n+1} ⟶ B_{n+1}` is a weak equivalence, so is the comparison
`B₀ ⊔_{A₀} colim A ⟶ colim B`. -/
theorem weakEquivalence_sequence_comparison (h1 : SequentialCofibrationAxiom C)
    (h2 : TrivialSequentialAxiom C) (hG : ∀ n, Cofibration (G.map (succHom n)))
    (hc : ∀ n, ∃ (P : C) (l : F.obj (n + 1) ⟶ P) (r : G.obj n ⟶ P) (c : P ⟶ G.obj (n + 1)),
      IsPushout (F.map (succHom n)) (τ.app n) l r ∧ l ≫ c = τ.app (n + 1) ∧
        r ≫ c = G.map (succHom n) ∧ WeakEquivalence c)
    [HasColimit F] [HasColimit G] {Q : C} {lQ : colimit F ⟶ Q} {rQ : G.obj 0 ⟶ Q}
    (hQ : IsPushout (colimit.ι F 0) (τ.app 0) lQ rQ) (k : Q ⟶ colimit G)
    (hk₁ : lQ ≫ k = colimMap τ) (hk₂ : rQ ≫ k = colimit.ι G 0) : WeakEquivalence k := by
  obtain ⟨_, hS, hs⟩ := prep τ hF0 hG0 hF
  have hFn := isCofibrant_obj_of_sequence F hF0 hF
  have hGn := isCofibrant_obj_of_sequence G hG0 hG
  have ha (n : ℕ) : Cofibration (a (F := F) n) := cofibration_map_of_le F hF0 hF (Nat.zero_le n)
  have hF' := hF
  have := h1.hasColimit (seq τ) (hS 0) hs
  -- every `φ_n` is a weak equivalence, by Lemma 9.3.3(1)(b)
  have hφ (n : ℕ) : WeakEquivalence (φ τ n) := by
    induction n with
    | zero =>
      have := isIso_φ_zero τ
      exact weakEquivalence_of_isIso _
    | succ n ih =>
      obtain ⟨P, l, r, c, hP, hl, hr, hcc⟩ := hc n
      exact weakEquivalence_comparison_comp (τ.naturality _) (isPushout τ n) hP
        (by rw [a_succ]; exact isPushout τ (n + 1)) (φ τ n) (inl_φ τ n) (inr_φ τ n)
        c hl hr (φ τ (n + 1)) (inl_φ τ (n + 1)) (by rw [inr_φ, ← G.map_comp]; rfl)
  have := weakEquivalence_colimMap_of_sequences h1 h2 (phi τ) (hS 0) hs hG0 hG hφ
  have := isIso_fromQ τ hQ
  have := weakEquivalence_of_isIso (fromQ τ hQ)
  rw [comparison_eq τ hQ k hk₁ hk₂]
  infer_instance

end Main

end ABCCofibrations.ABCPrecofibrationCategory
