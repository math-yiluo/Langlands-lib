/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtale
public import Mathlib.CategoryTheory.Limits.Comma

import Mathlib.RingTheory.Localization.Pi

/-! # Stability of ind-etale and principal ind-Zariski maps

Source: blueprint, proper base change, lemma "Stability and diagonal of an ind-etale algebra"
(blueprint: lemma-stability).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

-- Finite principal-localization blocks and their explicit base changes.
private def blocks (A : Type u) [CommRing A] : ObjectProperty (CommAlgCat.{u} A) :=
  fun B ↦ ∃ (n : ℕ) (f : Fin n → A),
    Nonempty (B ≃ₐ[A] ((j : Fin n) → Localization.Away (f j)))
open TensorProduct in
private noncomputable def tensorBlockEquiv (A S : Type u)
    [CommRing A] [CommRing S] [Algebra A S] (n : ℕ) (f : Fin n → A) :
    S ⊗[A] ((j : Fin n) → Localization.Away (f j)) ≃ₐ[S]
      ((j : Fin n) → Localization.Away (algebraMap A S (f j))) := by
  classical
  refine (Algebra.TensorProduct.piRight A S S _).trans (AlgEquiv.piCongrRight fun j ↦ ?_)
  have : IsLocalization.Away (algebraMap A S (f j)) (S ⊗[A] Localization.Away (f j)) := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      (inferInstance : IsLocalization
        (Algebra.algebraMapSubmonoid S (Submonoid.powers (f j)))
        (S ⊗[A] Localization.Away (f j)))
  exact IsLocalization.algEquiv (Submonoid.powers (algebraMap A S (f j))) _ _
open TensorProduct in
private theorem block_tensor (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    (B : CommAlgCat.{u} A) (hB : blocks A B) :
    blocks S (CommAlgCat.of S (S ⊗[A] B)) := by
  obtain ⟨n, f, ⟨e⟩⟩ := hB
  exact ⟨n, fun j ↦ algebraMap A S (f j),
    ⟨(Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e).trans
      (tensorBlockEquiv A S n f)⟩⟩
private noncomputable def bc (A S : Type u) [CommRing A] [CommRing S] [Algebra A S] :
    CommAlgCat.{u} A ⥤ CommAlgCat.{u} S :=
  (commAlgCatEquivUnder (.of A)).functor ⋙
    Under.pushout (CommRingCat.ofHom (algebraMap A S)) ⋙
      (commAlgCatEquivUnder (.of S)).inverse
open TensorProduct in
private noncomputable def bcEquiv (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    (B : CommAlgCat.{u} A) :
    (bc A S).obj B ≃ₐ[S] S ⊗[A] B := by
  let e := (CommRingCat.isPushout_tensorProduct A B S).isoPushout.symm
  exact
    { __ := e.commRingCatIsoToRingEquiv.trans (Algebra.TensorProduct.comm A B S).toRingEquiv
      commutes' := by
        intro s
        change (Algebra.TensorProduct.comm A B S)
          (e.hom.hom ((pushout.inr (CommRingCat.ofHom (algebraMap A B))
            (CommRingCat.ofHom (algebraMap A S))).hom s)) = _
        have he := (CommRingCat.isPushout_tensorProduct A B S).inr_isoPushout_inv
        have hes := congrArg (fun g ↦ g.hom s) he
        change e.hom.hom _ = 1 ⊗ₜ[A] s at hes
        exact (congrArg (Algebra.TensorProduct.comm A B S) hes).trans (by rfl) }

private theorem bc_preserves (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    {I : Type u} [SmallCategory I] : PreservesColimitsOfShape I (bc A S) := by
  unfold bc
  infer_instance
private theorem blocks_of_equiv (A : Type u) [CommRing A] {B C : CommAlgCat.{u} A}
    (e : B ≃ₐ[A] C) (h : blocks A C) : blocks A B := by
  obtain ⟨n, f, ⟨e'⟩⟩ := h
  exact ⟨n, f, ⟨e.trans e'⟩⟩
private theorem principal_of_equiv (A : Type u) [CommRing A]
    {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (e : B ≃ₐ[A] C) (h : Algebra.IsIndPrincipalZariski A B) :
    Algebra.IsIndPrincipalZariski A C := by
  change (blocks A).ind (CommAlgCat.of A C)
  exact (blocks A).ind.prop_of_iso (CommAlgCat.isoMk e) h
open TensorProduct in
private theorem principal_tensor (A S B : Type u) [CommRing A] [CommRing S] [CommRing B]
    [Algebra A S] [Algebra A B] (h : Algebra.IsIndPrincipalZariski A B) :
    Algebra.IsIndPrincipalZariski S (S ⊗[A] B) := by
  obtain ⟨I, _, _, P, hP⟩ := h
  have := bc_preserves A S (I := I)
  have h' : Algebra.IsIndPrincipalZariski S ((bc A S).obj (CommAlgCat.of A B)) := by
    refine ⟨I, ‹_›, ‹_›, P.map (bc A S), fun i ↦ ?_⟩
    change blocks S ((bc A S).obj (P.diag.obj i))
    exact blocks_of_equiv S (C := CommAlgCat.of S (S ⊗[A] P.diag.obj i))
      (bcEquiv A S (P.diag.obj i))
      (block_tensor A S (P.diag.obj i) (hP i))
  exact principal_of_equiv S (bcEquiv A S (CommAlgCat.of A B)) h'

private theorem principal_baseChange : RingHom.IsStableUnderBaseChange
    (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
      @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra) := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ hpush h
  rw [toAlgebra_algebraMap] at h ⊢
  have : Algebra.IsPushout R R' S S' := hpush.symm
  exact principal_of_equiv R' (Algebra.IsPushout.equiv R R' S S')
    (principal_tensor R R' S h)

-- Relate the algebra presentation to the categorical ind-property.
private local instance blocks_closedIso (A : Type u) [CommRing A] :
    (blocks A).IsClosedUnderIsomorphisms where
  of_iso e h := blocks_of_equiv A (CommAlgCat.algEquivOfIso e).symm h
private def blockMaps : MorphismProperty CommRingCat.{u} :=
  fun A B f ↦ let := f.hom.toAlgebra; blocks A (CommAlgCat.of A B)
private theorem principal_iff_ind {A B : CommRingCat.{u}} (f : A ⟶ B) :
    @Algebra.IsIndPrincipalZariski A B _ _ f.hom.toAlgebra ↔ blockMaps.ind.{u} f := by
  rw [MorphismProperty.ind_iff_ind_underMk]
  change (blocks A).ind ((commAlgCatEquivUnder A).inverse.obj (Under.mk f)) ↔ _
  change (blocks A).ind.inverseImage (commAlgCatEquivUnder A).inverse (Under.mk f) ↔ _
  rw [← ObjectProperty.ind_inverseImage_eq_of_isEquivalence
    (blocks A) (commAlgCatEquivUnder A).inverse]
  rfl
private theorem blockMaps_fp :
    blockMaps ≤ MorphismProperty.isFinitelyPresentable.{u} CommRingCat.{u} := by
  intro A B g hg
  apply CommRingCat.isFinitelyPresentable_under
  obtain ⟨n, f, ⟨e⟩⟩ := hg
  let := g.hom.toAlgebra
  have : Algebra.Etale A ((j : Fin n) → Localization.Away (f j)) := inferInstance
  have : Algebra.Etale A B := Algebra.Etale.of_equiv e.symm
  exact (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A B)).2
private theorem principal_iff_ind_principal {A B : CommRingCat.{u}} (f : A ⟶ B) :
    @Algebra.IsIndPrincipalZariski A B _ _ f.hom.toAlgebra ↔
      (RingHom.toMorphismProperty
        (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
          @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra)).ind.{u} f := by
  rw [principal_iff_ind]
  have heq : RingHom.toMorphismProperty
      (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
        @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra) = blockMaps.ind.{u} := by
    ext A B g
    exact principal_iff_ind g
  rw [heq]
  exact (congrArg (fun P : MorphismProperty CommRingCat.{u} ↦ P f)
    (MorphismProperty.ind_ind blockMaps_fp)).symm.to_iff

private local instance blockMaps_baseChange : blockMaps.{u}.IsStableUnderCobaseChange := by
  change (RingHom.toMorphismProperty
    (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
      let := f.toAlgebra; blocks A (CommAlgCat.of A B))).IsStableUnderCobaseChange
  apply RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ hpush h
  rw [toAlgebra_algebraMap] at h ⊢
  have : Algebra.IsPushout R R' S S' := hpush.symm
  exact blocks_of_equiv R' (Algebra.IsPushout.equiv R R' S S').symm
    (block_tensor R R' (CommAlgCat.of R S) h)

-- Localization and finite products preserve the blocks, including empty products.
private theorem block_away (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)
    (hB : blocks A B) (b : B) : blocks A (CommAlgCat.of A (Localization.Away b)) := by
  classical
  obtain ⟨n, f, ⟨e⟩⟩ := hB
  let R (i : Fin n) := Localization.Away (f i)
  let g : (i : Fin n) → R i := e b
  let T (i : Fin n) := Localization.Away (g i)
  have (i : Fin n) : IsLocalization ((Submonoid.powers g).map (Pi.evalRingHom R i))
      (T i) := by
    simp only [Submonoid.map_powers]
    change IsLocalization.Away (g i) (T i)
    infer_instance
  have : IsLocalization.Away g ((i : Fin n) → T i) :=
    (IsLocalization.iff_map_piEvalRingHom R ((i : Fin n) → T i)
      (Submonoid.powers g)).mpr inferInstance
  let e₁ : Localization.Away b ≃ₐ[A] Localization.Away g :=
    IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers b)
      (T := Submonoid.powers g) _ _ e (by rw [Submonoid.map_powers])
  let e₂ : Localization.Away g ≃ₐ[A] ((i : Fin n) → T i) :=
    (IsLocalization.algEquiv (Submonoid.powers g) _ _).restrictScalars A
  let a (i : Fin n) : A := (IsLocalization.Away.sec (f i) (g i)).1
  have (i : Fin n) : IsLocalization.Away (f i * a i) (T i) :=
    IsLocalization.Away.mul_of_associated (f i) (a i) (g i)
      (IsLocalization.Away.associated_sec_fst (f i) (g i))
  refine ⟨n, fun i ↦ f i * a i, ⟨e₁.trans (e₂.trans ?_)⟩⟩
  exact AlgEquiv.piCongrRight fun i ↦
    IsLocalization.algEquiv (Submonoid.powers (f i * a i)) _ _
private theorem block_pi (A : Type u) [CommRing A] {m : ℕ}
    (B : Fin m → CommAlgCat.{u} A) (hB : ∀ j, blocks A (B j)) :
    blocks A (CommAlgCat.of A ((j : Fin m) → B j)) := by
  classical
  choose n f e using hB
  let J := (j : Fin m) × Fin (n j)
  let fs : J → A := fun p ↦ f p.1 p.2
  let e₁ : ((j : Fin m) → B j) ≃ₐ[A]
      ((p : J) → Localization.Away (fs p)) :=
    { toFun x p := (e p.1).some (x p.1) p.2
      invFun x j := (e j).some.symm (fun k ↦ x ⟨j, k⟩)
      left_inv x := by ext j; exact (e j).some.symm_apply_apply (x j)
      right_inv x := by ext p; exact congrFun ((e p.1).some.apply_symm_apply _) p.2
      map_mul' x y := by ext p; simp
      map_add' x y := by ext p; simp
      commutes' a := by
        ext p
        simpa only [fs, Pi.algebraMap_apply] using congrFun ((e p.1).some.commutes a) p.2 }
  let k := Fintype.card J
  let eqv : Fin k ≃ J := (Fintype.equivFin J).symm
  refine ⟨k, fs ∘ eqv, ⟨e₁.trans ?_⟩⟩
  exact (AlgEquiv.piCongrLeft A (fun p : J ↦ Localization.Away (fs p)) eqv).symm
private theorem block_comp (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hB : blocks A (CommAlgCat.of A B)) (hC : blocks B (CommAlgCat.of B C)) :
    blocks A (CommAlgCat.of A C) := by
  obtain ⟨n, f, ⟨e⟩⟩ := hC
  apply blocks_of_equiv A
    (C := CommAlgCat.of A ((j : Fin n) → Localization.Away (f j))) (e.restrictScalars A)
  apply block_pi A (fun j ↦ CommAlgCat.of A (Localization.Away (f j)))
  intro j
  exact block_away A (CommAlgCat.of A B) hB (f j)

private local instance blockMaps_comp : blockMaps.{u}.IsStableUnderComposition where
  comp_mem {A B C} f g hf hg := by
    let := f.hom.toAlgebra
    let := g.hom.toAlgebra
    let := (g.hom.comp f.hom).toAlgebra
    have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
    exact block_comp A B C hf hg
-- Descend the finite list of denominators to one filtered stage.
private theorem finite_reps {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CommRingCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (n : ℕ) (x : Fin n → c.pt) :
    ∃ (i : I) (y : Fin n → D.obj i), ∀ j, (c.ι.app i).hom (y j) = x j := by
  classical
  choose i y hy using fun j ↦ Concrete.isColimit_exists_rep D hc (x j)
  let co := IsFiltered.cocone (Discrete.functor i)
  refine ⟨co.pt, fun j ↦ (D.map (co.ι.app ⟨j⟩)).hom (y j), fun j ↦ ?_⟩
  have hw := congrArg (fun k ↦ k.hom (y j)) (c.w (co.ι.app ⟨j⟩))
  exact hw.trans (hy j)
open TensorProduct in
private local instance blockMaps_spreads : MorphismProperty.PreIndSpreads.{u} blockMaps.{u} where
  exists_isPushout {I} _ _ {D} {c} hc {T} f hf := by
    let : Algebra c.pt T := f.hom.toAlgebra
    obtain ⟨n, g, ⟨e⟩⟩ := hf
    obtain ⟨i, gi, hgi⟩ := finite_reps D c hc n g
    let : Algebra (D.obj i) c.pt := (c.ι.app i).hom.toAlgebra
    let Ti := (j : Fin n) → Localization.Away (gi j)
    let e₀ : c.pt ⊗[D.obj i] Ti ≃ₐ[c.pt]
        ((j : Fin n) → Localization.Away (g j)) := by
      refine (tensorBlockEquiv (D.obj i) c.pt n gi).trans
        (AlgEquiv.piCongrRight fun j ↦ ?_)
      have hh : algebraMap (D.obj i) c.pt (gi j) = g j := hgi j
      rw [hh]
    let ebc : c.pt ⊗[D.obj i] Ti ≃ₐ[c.pt] T := e₀.trans e.symm
    let fi : D.obj i ⟶ CommRingCat.of Ti := CommRingCat.ofHom (algebraMap (D.obj i) Ti)
    let v : CommRingCat.of Ti ⟶ T := CommRingCat.ofHom
      (ebc.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
    refine ⟨i, CommRingCat.of Ti, fi, v, ?_, ?_⟩
    · refine (CommRingCat.isPushout_tensorProduct (D.obj i) c.pt Ti).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) ebc.toRingEquiv.toCommRingCatIso
        ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · ext x
        exact ebc.commutes x
      · rfl
    · change @blocks (D.obj i) _
        (@CommAlgCat.of (D.obj i) _ Ti _ (algebraMap (D.obj i) Ti).toAlgebra)
      rw [toAlgebra_algebraMap]
      exact ⟨n, gi, ⟨AlgEquiv.refl⟩⟩

private theorem principal_comp : RingHom.StableUnderComposition
    (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
      @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra) := by
  have : blockMaps.ind.{u}.IsStableUnderComposition :=
    .ind_of_le_isFinitelyPresentable blockMaps_fp
  intro A B C _ _ _ f g hf hg
  exact (principal_iff_ind (CommRingCat.ofHom (g.comp f))).mpr
    (blockMaps.ind.comp_mem (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      ((principal_iff_ind (CommRingCat.ofHom f)).mp hf)
      ((principal_iff_ind (CommRingCat.ofHom g)).mp hg))

-- Push out to a fixed source, then construct the colimit universal property.
private theorem colimit_mem_ind {C : Type (u + 1)} [Category.{u} C] [HasPushouts C]
    (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F G : I ⥤ C) (a : Cocone F) (b : Cocone G)
    (ha : IsColimit a) (hb : IsColimit b) (η : F ⟶ G)
    (hη : ∀ i, P (η.app i)) (f : a.pt ⟶ b.pt)
    (hf : ∀ i, a.ι.app i ≫ f = η.app i ≫ b.ι.app i) : P.ind.{u} f := by
  let E : I ⥤ C :=
    { obj i := pushout (a.ι.app i) (η.app i)
      map {i j} k := pushout.desc (pushout.inl _ _)
        (G.map k ≫ pushout.inr _ _) (by
          rw [← Category.assoc, ← η.naturality k]
          simp only [Category.assoc, ← pushout.condition]
          rw [← Category.assoc, a.w k])
      map_id i := by apply pushout.hom_ext <;> simp
      map_comp {i j k} x y := by apply pushout.hom_ext <;> simp }
  have hinl {i j : I} (k : i ⟶ j) :
      pushout.inl (a.ι.app i) (η.app i) ≫ E.map k =
        pushout.inl (a.ι.app j) (η.app j) := by simp [E]
  have hinr {i j : I} (k : i ⟶ j) :
      pushout.inr (a.ι.app i) (η.app i) ≫ E.map k =
        G.map k ≫ pushout.inr (a.ι.app j) (η.app j) := by simp [E]
  have hinlw : ∀ (w : Cocone E) {i j : I} (k : i ⟶ j),
      pushout.inl (a.ι.app i) (η.app i) ≫ w.ι.app i =
        pushout.inl (a.ι.app j) (η.app j) ≫ w.ι.app j := by
    intro w i j k
    rw [← w.w k, ← Category.assoc, hinl k]
  have hleft (w : Cocone E) (i j : I) :
      pushout.inl (a.ι.app i) (η.app i) ≫ w.ι.app i =
        pushout.inl (a.ι.app j) (η.app j) ≫ w.ι.app j :=
    (hinlw w (IsFiltered.leftToMax i j)).trans
      (hinlw w (IsFiltered.rightToMax i j)).symm
  let rightCocone (w : Cocone E) : Cocone G :=
    { pt := w.pt
      ι :=
        { app i := pushout.inr _ _ ≫ w.ι.app i
          naturality {i j} k := by
            dsimp
            rw [Category.comp_id, ← Category.assoc, ← hinr k, Category.assoc, w.w k] } }
  let t : (Functor.const I).obj a.pt ⟶ E :=
    { app i := pushout.inl _ _
      naturality {i j} k := by dsimp; rw [Category.id_comp, hinl k] }
  let s : E ⟶ (Functor.const I).obj b.pt :=
    { app i := pushout.desc f (b.ι.app i) (hf i)
      naturality {i j} k := by apply pushout.hom_ext <;> simp [E] }
  refine ⟨I, ‹_›, ‹_›, E, t, s, ?_, fun i ↦ ⟨P.pushout_inl _ _ (hη i), by simp [t, s]⟩⟩
  refine
    { desc := fun w ↦ hb.desc (rightCocone w)
      fac := fun w i ↦ ?_
      uniq := fun w m hm ↦ ?_ }
  · dsimp only
    apply pushout.hom_ext
    · simp only [s, pushout.inl_desc_assoc]
      change f ≫ hb.desc (rightCocone w) = pushout.inl _ _ ≫ w.ι.app i
      apply ha.hom_ext
      intro j
      rw [← Category.assoc, hf j, Category.assoc, hb.fac]
      dsimp [rightCocone]
      rw [hleft w i j, ← pushout.condition_assoc]
    · simp only [s, pushout.inr_desc_assoc]
      change b.ι.app i ≫ hb.desc (rightCocone w) = _
      exact hb.fac _ i
  · apply hb.hom_ext
    intro i
    rw [hb.fac]
    have hi := congrArg (fun g ↦ pushout.inr (a.ι.app i) (η.app i) ≫ g) (hm i)
    simpa [s, rightCocone] using hi
private theorem indEtale_colimit {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Arrow CommRingCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (h : ∀ i, (D.obj i).hom.hom.IndEtale) : c.pt.hom.hom.IndEtale := by
  have : (RingHom.toMorphismProperty (@RingHom.IndEtale.{u})).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
      RingHom.IndEtale.isStableUnderBaseChange
  have h' := colimit_mem_ind (RingHom.toMorphismProperty (@RingHom.IndEtale.{u}))
    (D ⋙ Arrow.leftFunc) (D ⋙ Arrow.rightFunc)
    (Arrow.leftFunc.mapCocone c) (Arrow.rightFunc.mapCocone c)
    (isColimitOfPreserves Arrow.leftFunc hc) (isColimitOfPreserves Arrow.rightFunc hc)
    { app i := (D.obj i).hom
      naturality i j f := (D.map f).w }
    h c.pt.hom (fun i ↦ (c.ι.app i).w)
  exact (RingHom.IndEtale.iff_ind_indEtale c.pt.hom.hom).mpr h'

private theorem principal_colimit {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Arrow CommRingCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (h : ∀ i, @Algebra.IsIndPrincipalZariski (D.obj i).left (D.obj i).right
      _ _ (D.obj i).hom.hom.toAlgebra) :
    @Algebra.IsIndPrincipalZariski c.pt.left c.pt.right _ _ c.pt.hom.hom.toAlgebra := by
  have : (RingHom.toMorphismProperty
      (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
        @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra)).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr principal_baseChange
  have h' := colimit_mem_ind (RingHom.toMorphismProperty
      (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
        @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra))
    (D ⋙ Arrow.leftFunc) (D ⋙ Arrow.rightFunc)
    (Arrow.leftFunc.mapCocone c) (Arrow.rightFunc.mapCocone c)
    (isColimitOfPreserves Arrow.leftFunc hc) (isColimitOfPreserves Arrow.rightFunc hc)
    { app i := (D.obj i).hom
      naturality i j f := (D.map f).w }
    h c.pt.hom (fun i ↦ (c.ι.app i).w)
  exact (principal_iff_ind_principal c.pt.hom).mpr h'

-- The remaining clauses use existing ind-etale and weakly etale APIs.
private theorem weaklyEtale_of_bijective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Bijective f) : f.WeaklyEtale := by
  let := f.toAlgebra
  have : Algebra.Etale R S := (RingHom.Etale.of_bijective hf).toAlgebra
  exact inferInstanceAs (Algebra.WeaklyEtale R S)
private theorem weaklyEtale_baseChange :
    RingHom.IsStableUnderBaseChange (@RingHom.WeaklyEtale.{u,u}) := by
  apply RingHom.IsStableUnderBaseChange.mk
  · apply RingHom.StableUnderComposition.respectsIso
    · intro R S T _ _ _ f g hf hg
      exact hf.comp hg
    · intro R S _ _ e
      exact weaklyEtale_of_bijective _ e.bijective
  · intro R S T _ _ _ _ _ h
    rw [RingHom.weaklyEtale_algebraMap_iff] at h ⊢
    have := h
    infer_instance
private theorem relative_indEtale
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (hB : Algebra.IndEtale A B)
    (hC : Algebra.IndEtale A C) (f : B →ₐ[A] C) : f.toRingHom.IndEtale := by
  apply RingHom.IndEtale.of_comp ((RingHom.IndEtale.algebraMap_iff A B).mpr hB)
  have heq : f.toRingHom.comp (algebraMap A B) = algebraMap A C :=
    RingHom.ext f.commutes
  rw [heq]
  exact (RingHom.IndEtale.algebraMap_iff A C).mpr hC

namespace RingHom

/-- Stability under base change, composition and filtered colimits of ind-etale and principal
ind-Zariski maps; weak etaleness of ind-etale maps; the relative ind-etale assertion; and
composition and base-change stability of weakly etale maps.
Source: blueprint, proper base change, lemma "Stability and diagonal of an ind-etale algebra"
(blueprint: lemma-stability).

Filtered colimits are expressed in the arrow category, allowing varying source rings.
The principal ind-Zariski condition is evaluated using the algebra structure of each ring map.

Proof:

The source library already proves ind-etale base change and composition, weak etaleness of
ind-etale maps, relative ind-etaleness by cancellation, and weakly etale composition. Weakly
etale base change follows from the tensor-product instance and invariance under ring isomorphism.

For principal ind-Zariski maps, use finite products of principal localizations as building
blocks. Tensor product preserves these blocks: it distributes over finite products and changes
localization at f into localization at the image of f. The base-change functor on algebra
categories preserves colimits, giving base-change stability of their filtered colimits.

The blocks are finitely presented because they are etale. They compose: localizing a product
amounts to localizing each factor, and if g = a/f^N in A_f then (A_f)_g is A_(fa). Flatten the
resulting finite product. They also spread over filtered colimits: finitely many denominators
have representatives at a common stage. Apply the source library's composition theorem for
ind-properties of finitely presented morphisms that spread.

For filtered colimits with varying bases, push each stage arrow out to the colimit source.
These pushouts form a filtered diagram with that fixed source, whose target colimit is the
original target colimit. Construct its universal property using the two original colimit
universal properties and pushout descent; filteredness identifies all the source injections.
Cobase-change stability makes its stages satisfy the original property, so the colimit arrow
satisfies its ind-property. Finally flatten twice-ind presentations, using
`RingHom.IndEtale.iff_ind_indEtale` and `MorphismProperty.ind_ind`, respectively.
-/
theorem indEtale_principalZariski_stability :
    RingHom.IsStableUnderBaseChange (@RingHom.IndEtale.{u}) ∧
    RingHom.IsStableUnderBaseChange
      (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
        @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra) ∧
    RingHom.StableUnderComposition (@RingHom.IndEtale.{u}) ∧
    RingHom.StableUnderComposition
      (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
        @Algebra.IsIndPrincipalZariski A B _ _ f.toAlgebra) ∧
    (∀ (I : Type u) [SmallCategory I] [IsFiltered I]
      (D : I ⥤ Arrow CommRingCat.{u}) (c : Cocone D), IsColimit c →
      (∀ i : I, (D.obj i).hom.hom.IndEtale) → c.pt.hom.hom.IndEtale) ∧
    (∀ (I : Type u) [SmallCategory I] [IsFiltered I]
      (D : I ⥤ Arrow CommRingCat.{u}) (c : Cocone D), IsColimit c →
      (∀ i : I, @Algebra.IsIndPrincipalZariski (D.obj i).left (D.obj i).right
        _ _ (D.obj i).hom.hom.toAlgebra) →
      @Algebra.IsIndPrincipalZariski c.pt.left c.pt.right _ _ c.pt.hom.hom.toAlgebra) ∧
    (∀ (A B : Type u) [CommRing A] [CommRing B] (f : A →+* B),
      f.IndEtale → f.WeaklyEtale) ∧
    (∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra A C], Algebra.IndEtale A B → Algebra.IndEtale A C →
      ∀ f : B →ₐ[A] C, f.toRingHom.IndEtale) ∧
    RingHom.StableUnderComposition (@RingHom.WeaklyEtale.{u, u}) ∧
    RingHom.IsStableUnderBaseChange (@RingHom.WeaklyEtale.{u, u}) := by
  refine ⟨IndEtale.isStableUnderBaseChange, principal_baseChange, ?_, principal_comp,
    ?_, ?_, ?_, ?_, ?_, weaklyEtale_baseChange⟩
  · intro A B C _ _ _ f g hf hg
    exact hg.comp hf
  · intro I _ _ D c hc h
    exact indEtale_colimit D c hc h
  · intro I _ _ D c hc h
    exact principal_colimit D c hc h
  · intro A B _ _ f hf
    exact hf.weaklyEtale
  · intro A B C _ _ _ _ _ hB hC f
    exact relative_indEtale A B C hB hC f
  · intro A B C _ _ _ f g hf hg
    exact hf.comp hg

end RingHom
