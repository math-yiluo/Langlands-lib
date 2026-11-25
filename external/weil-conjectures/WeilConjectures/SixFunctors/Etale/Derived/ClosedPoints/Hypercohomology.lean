/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.MinimalCohomology

/-!
# Cohomology of complexes with acyclic cohomology objects

Let `F : C ⥤ D` be a left exact functor, `C` with enough injectives and K-injective
resolutions, and `K ∈ D^{≥ m}(C)` all of whose homology objects `H^q(K)` are `F`-acyclic
(`R^p F(H^q K) = 0` for `p > 0`). Then `H^n(RF(K)) ≅ F(H^n K)` for all `n`: by induction on the
length, a bounded complex `L ∈ D^{≤ a}` with `F`-acyclic homology has `H^j(RF(L)) = 0` for
`j > a`, and the truncation triangles then identify `H^n(RF(K))` with
`H^n(RF(H^n(K)[-n])) = F(H^n K)`.

## Main statements

- `CategoryTheory.Functor.nonempty_homology_rightDerivedFunctor_obj_iso_of_acyclic`.
- `AlgebraicGeometry.Etale.nonempty_homology_rightDerivedGlobalSections_obj_iso_of_acyclic`
  (`lem-kun-0bkz`, bounded below case).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]

/-- `H^j(RF(M[-a])) ≅ H^{j - a}(RF(M[0]))`. -/
noncomputable def homologyRightDerivedFunctorObjSingleFunctorShiftIso (M : C) (a j : ℤ) :
    (DerivedCategory.homologyFunctor D j).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C a).obj M)) ≅
      (DerivedCategory.homologyFunctor D (j - a)).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M)) :=
  (DerivedCategory.homologyFunctor D j).mapIso
      (F.rightDerivedFunctor.mapIso
        (((DerivedCategory.singleFunctors C).shiftIso (-a) a 0 (by omega)).app M).symm) ≪≫
    (DerivedCategory.homologyFunctor D j).mapIso
      ((F.rightDerivedFunctor.commShiftIso (-a)).app
        ((DerivedCategory.singleFunctor C 0).obj M)) ≪≫
    ((DerivedCategory.homologyFunctor D 0).shiftIso (-a) j (j - a) (by omega)).app
      (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M))

/-- An object `M` of `C` is `F`-acyclic if `H^p(RF(M[0])) = 0` for `p > 0`. -/
def IsRightAcyclic (M : C) : Prop :=
  ∀ p : ℤ, 0 < p → IsZero ((DerivedCategory.homologyFunctor D p).obj
    (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M)))

variable {F}

omit [EnoughInjectives C] in
lemma IsRightAcyclic.of_iso {M M' : C} (e : M ≅ M') (h : F.IsRightAcyclic M') :
    F.IsRightAcyclic M := fun p hp ↦
  (h p hp).of_iso ((DerivedCategory.homologyFunctor D p).mapIso
    (F.rightDerivedFunctor.mapIso ((DerivedCategory.singleFunctor C 0).mapIso e)))

omit [EnoughInjectives C] in
lemma IsRightAcyclic.of_isZero {M : C} (hM : IsZero M) : F.IsRightAcyclic M := fun p _ ↦
  (DerivedCategory.homologyFunctor D p).map_isZero
    (F.isZero_rightDerivedFunctor_obj ((DerivedCategory.singleFunctor C 0).map_isZero hM))

variable (F)

omit [EnoughInjectives C] in
/-- A bounded complex `L ∈ D^{≥ a + 1 - k} ∩ D^{≤ a}` whose homology objects are `F`-acyclic
has `H^j(RF(L)) = 0` for `j > a`. -/
theorem isZero_homology_rightDerivedFunctor_obj_of_isLE (k : ℕ) :
    ∀ (L : DerivedCategory C) (a : ℤ), L.IsGE (a + 1 - k) → L.IsLE a →
      (∀ q, F.IsRightAcyclic ((DerivedCategory.homologyFunctor C q).obj L)) →
        ∀ j, a < j → IsZero ((DerivedCategory.homologyFunctor D j).obj
          (F.rightDerivedFunctor.obj L)) := by
  let t := DerivedCategory.TStructure.t (C := C)
  induction k with
  | zero =>
    intro L a h₁ h₂ _ j _
    have hL : IsZero L := (DerivedCategory.isZero_iff L).2 fun q ↦ by
      rcases le_or_gt q a with hq | hq
      · exact DerivedCategory.isZero_of_isGE L (a + 1 - (0 : ℕ)) q (by push_cast; omega)
      · exact DerivedCategory.isZero_of_isLE L a q hq
    exact (DerivedCategory.homologyFunctor D j).map_isZero (F.isZero_rightDerivedFunctor_obj hL)
  | succ k ih =>
    intro L a h₁ h₂ hL j hj
    let T := (t.triangleLTGE a).obj L
    have hT : T ∈ distTriang _ := t.triangleLTGE_distinguished a L
    let R := F.rightDerivedFunctor
    have hRT := R.map_distinguished T hT
    -- the first term
    have : T.obj₁.IsGE (a + 1 - (k + 1 : ℕ)) :=
      (inferInstance : ((t.truncLT a).obj L).IsGE (a + 1 - (k + 1 : ℕ)))
    have h₁' : T.obj₁.IsGE (a - 1 + 1 - k) := t.isGE_of_ge _ _ (a + 1 - (k + 1 : ℕ))
      (by push_cast; omega)
    have h₁'' : T.obj₁.IsLE (a - 1) := inferInstance
    have hac₁ (q : ℤ) :
        F.IsRightAcyclic ((DerivedCategory.homologyFunctor C q).obj T.obj₁) := by
      rcases lt_or_ge q a with hq | hq
      · have : IsIso ((DerivedCategory.homologyFunctor C q).map T.mor₁) :=
          DerivedCategory.isIso_homologyFunctor_map_truncLTι_app L a q hq
        exact (hL q).of_iso (asIso ((DerivedCategory.homologyFunctor C q).map T.mor₁))
      · exact IsRightAcyclic.of_isZero (DerivedCategory.isZero_of_isLE _ (a - 1) q (by omega))
    have hz₁ := ih T.obj₁ (a - 1) h₁' h₁'' hac₁ j (by omega)
    -- the third term
    have : T.obj₃.IsGE a := inferInstance
    have : T.obj₃.IsLE a := (inferInstance : ((t.truncGE a).obj L).IsLE a)
    obtain ⟨A, ⟨e⟩⟩ := T.obj₃.exists_iso_singleFunctor_obj_of_isGE_of_isLE a
    have : IsIso ((DerivedCategory.homologyFunctor C a).map T.mor₂) :=
      DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app L a a le_rfl
    let eA : A ≅ (DerivedCategory.homologyFunctor C a).obj L :=
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C a).app A).symm ≪≫
        (DerivedCategory.homologyFunctor C a).mapIso e.symm ≪≫
          (asIso ((DerivedCategory.homologyFunctor C a).map T.mor₂)).symm
    have hz₃ : IsZero ((DerivedCategory.homologyFunctor D j).obj (R.obj T.obj₃)) :=
      ((hL a).of_iso eA (j - a) (by omega)).of_iso
        ((DerivedCategory.homologyFunctor D j).mapIso (R.mapIso e) ≪≫
          F.homologyRightDerivedFunctorObjSingleFunctorShiftIso A a j)
    exact ((DerivedCategory.homologyFunctor D 0).homologySequence_exact₂ _ hRT j).isZero_X₂
      (hz₁.eq_of_src _ _) (hz₃.eq_of_tgt _ _)

variable [PreservesFiniteLimits F]

/-- **Cohomology of a complex with acyclic homology.** For a left exact functor `F` and
`K ∈ D^{≥ m}(C)` whose homology objects are `F`-acyclic, `H^n(RF(K)) ≅ F(H^n K)` for all
`n`. -/
theorem nonempty_homology_rightDerivedFunctor_obj_iso_of_acyclic (K : DerivedCategory C)
    (m : ℤ) [K.IsGE m]
    (hK : ∀ q, F.IsRightAcyclic ((DerivedCategory.homologyFunctor C q).obj K))
    (n : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor D n).obj (F.rightDerivedFunctor.obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor C n).obj K)) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let R := F.rightDerivedFunctor
  -- `H^n(RF(K)) ≅ H^n(RF(τ_{≤ n} K))`
  let T := (t.triangleLTGE (n + 1)).obj K
  have hT : T ∈ distTriang _ := t.triangleLTGE_distinguished (n + 1) K
  have hRT := R.map_distinguished T hT
  have h₃ : (R.obj T.obj₃).IsGE (n + 1) := F.isGE_rightDerivedFunctor_obj _ _
  have hmono : Mono ((DerivedCategory.homologyFunctor D n).map (R.map T.mor₁)) :=
    ((DerivedCategory.homologyFunctor D 0).homologySequence_mono_shift_map_mor₁_iff _ hRT
      (n - 1) n (by lia)).2
        (IsZero.eq_of_src (DerivedCategory.isZero_of_isGE (R.obj T.obj₃) (n + 1) _ (by lia)) _ _)
  have hepi : Epi ((DerivedCategory.homologyFunctor D n).map (R.map T.mor₁)) :=
    ((DerivedCategory.homologyFunctor D 0).homologySequence_epi_shift_map_mor₁_iff _ hRT n).2
      (IsZero.eq_of_tgt (DerivedCategory.isZero_of_isGE (R.obj T.obj₃) (n + 1) _ (by lia)) _ _)
  have : IsIso ((DerivedCategory.homologyFunctor D n).map (R.map T.mor₁)) :=
    isIso_of_mono_of_epi _
  -- `L = τ_{≤ n} K`
  let L := T.obj₁
  have hLn : L.IsLE n := t.isLE_of_le _ (n + 1 - 1) n (by lia)
  have hLm : L.IsGE m := (inferInstance : ((t.truncLT (n + 1)).obj K).IsGE m)
  have hLH (q : ℤ) (hq : q ≤ n) : IsIso ((DerivedCategory.homologyFunctor C q).map T.mor₁) :=
    DerivedCategory.isIso_homologyFunctor_map_truncLTι_app K (n + 1) q (by lia)
  -- `H^n(RF(L)) ≅ H^n(RF(τ_{≥ n} L))`
  let T' := (t.triangleLTGE n).obj L
  have hT' : T' ∈ distTriang _ := t.triangleLTGE_distinguished n L
  have hRT' := R.map_distinguished T' hT'
  have hac₁ (q : ℤ) :
      F.IsRightAcyclic ((DerivedCategory.homologyFunctor C q).obj T'.obj₁) := by
    rcases lt_or_ge q n with hq | hq
    · have : IsIso ((DerivedCategory.homologyFunctor C q).map T'.mor₁) :=
        DerivedCategory.isIso_homologyFunctor_map_truncLTι_app L n q hq
      have := hLH q (by lia)
      exact (hK q).of_iso (asIso ((DerivedCategory.homologyFunctor C q).map T'.mor₁) ≪≫
        asIso ((DerivedCategory.homologyFunctor C q).map T.mor₁))
    · exact IsRightAcyclic.of_isZero (DerivedCategory.isZero_of_isLE _ (n - 1) q (by omega))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (n - 1) + 1 - k ≤ m := ⟨(n - m).toNat, by omega⟩
  have : T'.obj₁.IsGE m := (inferInstance : ((t.truncLT n).obj L).IsGE m)
  have hge : T'.obj₁.IsGE ((n - 1) + 1 - k) := t.isGE_of_ge _ _ m hk
  have hvan := F.isZero_homology_rightDerivedFunctor_obj_of_isLE k T'.obj₁ (n - 1) hge
    inferInstance hac₁
  have hmono' : Mono ((DerivedCategory.homologyFunctor D n).map (R.map T'.mor₂)) :=
    ((DerivedCategory.homologyFunctor D 0).homologySequence_mono_shift_map_mor₂_iff _ hRT' n).2
      ((hvan n (by lia)).eq_of_src _ _)
  have hepi' : Epi ((DerivedCategory.homologyFunctor D n).map (R.map T'.mor₂)) :=
    ((DerivedCategory.homologyFunctor D 0).homologySequence_epi_shift_map_mor₂_iff _ hRT' n
      (n + 1) rfl).2 ((hvan (n + 1) (by lia)).eq_of_tgt _ _)
  have : IsIso ((DerivedCategory.homologyFunctor D n).map (R.map T'.mor₂)) :=
    isIso_of_mono_of_epi _
  -- `τ_{≥ n} L` is `H^n(K)` placed in degree `n`
  have : T'.obj₃.IsLE n := (inferInstance : ((t.truncGE n).obj L).IsLE n)
  obtain ⟨A, ⟨e⟩⟩ := T'.obj₃.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  have : IsIso ((DerivedCategory.homologyFunctor C n).map T'.mor₂) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app L n n le_rfl
  have := hLH n le_rfl
  let eA : A ≅ (DerivedCategory.homologyFunctor C n).obj K :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C n).app A).symm ≪≫
      (DerivedCategory.homologyFunctor C n).mapIso e.symm ≪≫
        (asIso ((DerivedCategory.homologyFunctor C n).map T'.mor₂)).symm ≪≫
          asIso ((DerivedCategory.homologyFunctor C n).map T.mor₁)
  exact ⟨(asIso ((DerivedCategory.homologyFunctor D n).map (R.map T.mor₁))).symm ≪≫
    asIso ((DerivedCategory.homologyFunctor D n).map (R.map T'.mor₂)) ≪≫
      (DerivedCategory.homologyFunctor D n).mapIso (R.mapIso e) ≪≫
        F.homologyRightDerivedFunctorObjSingleFunctorIsoSelf A n ≪≫ F.mapIso eA⟩

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-kun-0bkz`: **cohomology of complexes with acyclic cohomology sheaves**
(bounded below case, for the global sections over `X` itself). Let `X` be a scheme and
`K ∈ D^{≥ m}(X_ét, Λ)` such that `H^p(X_ét, ℋ^q(K)) = 0` for all `p > 0` and all `q`. Then
`H^q(X_ét, K) ≅ H^0(X_ét, ℋ^q(K))` for all `q`. Applied to the restrictions of `K` to the
members `U` of a class `B` of étale `X`-schemes this gives the blueprint's statement for bounded
below `K`; the unbounded case, which needs derived limits, is not treated. -/
theorem nonempty_homology_rightDerivedGlobalSections_obj_iso_of_acyclic (X : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m : ℤ)
    [K.IsGE m]
    (hK : ∀ q p : ℤ, 0 < p → IsZero ((_root_.DerivedCategory.homologyFunctor _ p).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((_root_.DerivedCategory.homologyFunctor _ q).obj K))))) (q : ℤ) :
    Nonempty ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K) ≅
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) :=
  (Sheaf.Γ X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).nonempty_homology_rightDerivedFunctor_obj_iso_of_acyclic K m
      (fun q p hp ↦ hK q p hp) q

end AlgebraicGeometry.Etale
